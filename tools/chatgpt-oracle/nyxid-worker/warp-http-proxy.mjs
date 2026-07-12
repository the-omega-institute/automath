import net from "node:net";

const listenAddress = process.argv[2] ?? "127.0.0.1";
const listenPort = Number(process.argv[3] ?? "40002");
const socksAddress = process.argv[4] ?? "127.0.0.1";
const socksPort = Number(process.argv[5] ?? "40000");

function encodeSocksAddress(host) {
  const v4 = net.isIPv4(host);
  const v6 = net.isIPv6(host);
  if (v4) {
    return Buffer.concat([Buffer.from([0x01]), Buffer.from(host.split(".").map(Number))]);
  }
  if (v6) {
    const sections = host.split(":");
    const bytes = [];
    for (const section of sections) {
      const value = Number.parseInt(section || "0", 16);
      bytes.push((value >> 8) & 0xff, value & 0xff);
    }
    return Buffer.concat([Buffer.from([0x04]), Buffer.from(bytes)]);
  }

  const domain = Buffer.from(host, "utf8");
  if (domain.length > 255) {
    throw new Error(`SOCKS domain too long: ${host}`);
  }
  return Buffer.concat([Buffer.from([0x03, domain.length]), domain]);
}

function readExact(socket, length) {
  return new Promise((resolve, reject) => {
    let buffer = Buffer.alloc(0);

    function cleanup() {
      socket.off("data", onData);
      socket.off("error", onError);
      socket.off("close", onClose);
    }

    function onData(chunk) {
      buffer = Buffer.concat([buffer, chunk]);
      if (buffer.length >= length) {
        cleanup();
        const wanted = buffer.subarray(0, length);
        const extra = buffer.subarray(length);
        if (extra.length > 0) {
          socket.unshift(extra);
        }
        resolve(wanted);
      }
    }

    function onError(error) {
      cleanup();
      reject(error);
    }

    function onClose() {
      cleanup();
      reject(new Error("socket closed"));
    }

    socket.on("data", onData);
    socket.on("error", onError);
    socket.on("close", onClose);
  });
}

async function connectViaSocks(host, port) {
  const socket = net.connect(socksPort, socksAddress);
  socket.on("error", (error) => {
    console.error(`SOCKS socket error for ${host}:${port}: ${error.message}`);
  });
  await new Promise((resolve, reject) => {
    socket.once("connect", resolve);
    socket.once("error", (error) => reject(error));
  });

  console.error(`SOCKS greeting ${host}:${port}`);
  socket.write(Buffer.from([0x05, 0x01, 0x00]));
  const greeting = await readExact(socket, 2);
  console.error(`SOCKS greeting response ${host}:${port}: ${greeting.toString("hex")}`);
  if (greeting[0] !== 0x05 || greeting[1] !== 0x00) {
    socket.destroy();
    throw new Error("SOCKS5 server rejected no-auth greeting");
  }

  const address = encodeSocksAddress(host);
  const portBuffer = Buffer.alloc(2);
  portBuffer.writeUInt16BE(port);
  console.error(`SOCKS connect ${host}:${port}`);
  socket.write(Buffer.concat([Buffer.from([0x05, 0x01, 0x00]), address, portBuffer]));

  const header = await readExact(socket, 4);
  console.error(`SOCKS connect response ${host}:${port}: ${header.toString("hex")}`);
  if (header[0] !== 0x05 || header[1] !== 0x00) {
    socket.destroy();
    throw new Error(`SOCKS5 connect failed with code ${header[1]}`);
  }

  return socket;
}

const server = net.createServer((client) => {
  let header = Buffer.alloc(0);
  client.on("error", (error) => {
    console.error(`client socket error: ${error.message}`);
  });

  client.on("data", async function onInitialData(chunk) {
    header = Buffer.concat([header, chunk]);
    const end = header.indexOf("\r\n\r\n");
    if (end === -1) {
      return;
    }

    client.off("data", onInitialData);
    const requestText = header.subarray(0, end).toString("latin1");
    const rest = header.subarray(end + 4);
    const [requestLine] = requestText.split("\r\n");
    const [method, target] = requestLine.split(" ");

    if (method !== "CONNECT" || !target) {
      client.end("HTTP/1.1 405 Method Not Allowed\r\nConnection: close\r\n\r\n");
      return;
    }

    const splitAt = target.lastIndexOf(":");
    const host = splitAt === -1 ? target : target.slice(0, splitAt);
    const port = splitAt === -1 ? 443 : Number(target.slice(splitAt + 1));

    try {
      const upstream = await connectViaSocks(host, port);
      upstream.on("error", () => client.destroy());
      client.write("HTTP/1.1 200 Connection Established\r\nProxy-Agent: nyxid-warp\r\n\r\n");
      if (rest.length > 0) {
        upstream.write(rest);
      }

      client.on("error", () => upstream.destroy());
      client.on("close", () => upstream.destroy());
      upstream.on("close", () => client.destroy());
      client.pipe(upstream);
      upstream.pipe(client);
    } catch (error) {
      console.error(`CONNECT ${host}:${port} failed: ${error.message}`);
      client.end(`HTTP/1.1 502 Bad Gateway\r\nConnection: close\r\n\r\n${error.message}`);
    }
  });
});

server.on("error", (error) => {
  console.error(error.message);
  process.exit(1);
});

server.listen(listenPort, listenAddress, () => {
  console.log(`HTTP CONNECT proxy ${listenAddress}:${listenPort} -> SOCKS5 ${socksAddress}:${socksPort}`);
});
