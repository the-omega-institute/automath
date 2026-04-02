// ==UserScript==
// @name         ChatGPT Oracle Test
// @namespace    omega-automath
// @version      0.1
// @description  Minimal test — just shows a panel on chatgpt.com
// @match        https://chatgpt.com/*
// @grant        none
// @run-at       document-idle
// ==/UserScript==

(function () {
  "use strict";

  // Create visible panel immediately
  function showPanel() {
    const panel = document.createElement("div");
    panel.style.cssText =
      "position:fixed; bottom:20px; right:20px; z-index:999999; " +
      "background:red; color:white; padding:16px 24px; border-radius:8px; " +
      "font-size:16px; font-family:monospace; box-shadow:0 4px 20px rgba(0,0,0,0.5);";
    panel.textContent = "[Oracle Test] Script is running! " + new Date().toLocaleTimeString();
    document.body.appendChild(panel);
    console.log("[oracle-test] Panel created successfully");
  }

  // Try immediately
  if (document.body) {
    showPanel();
  } else {
    document.addEventListener("DOMContentLoaded", showPanel);
  }

  console.log("[oracle-test] Script loaded at: " + new Date().toISOString());
})();
