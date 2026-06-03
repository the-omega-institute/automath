# Rule 110 论文研究报告

引用格式：`PDF page` 指 `pdftotext -layout` 产生的分页；`line` 指同一抽取文本的 `nl -ba` 行号。凡 PDF 文本把 `B̄`、`Ē`、`B̂` 或上标抽乱，条目后显式标注视觉核对需求。

## Part 1: Cook construction

### 1.1 理论主张

Cook 2009 的编译链是 Turing machine → tag system → cyclic tag system → Rule 110 state。论文摘要说 Rule 110 emulates a Turing machine “by encoding the Turing machine and its tape into a repeating left pattern, a central pattern, and a repeating right pattern”，并说明文章给出 explicit compiler（Cook 2009, PDF page 1, abstract, lines 17-20）。Section 1.2 把 TM 转成 deletion number `s` 的 tag system（Cook 2009, PDF page 2-3, §1.2, lines 78-159）；Section 1.3 把 tag rules unary-encoded 成 cyclic tag appendants, cyclic list 长度为 `s|Φ|`（Cook 2009, PDF page 3, §1.3, lines 163-184）；Section 1.4 把 CTS tape/appendants glue 成 Rule 110 initial state（Cook 2009, PDF page 3-7, §1.4, lines 187-303）。

Polynomial bound 的原文锚点有两处。摘要写 “polynomial time is required” and uses Neary and Woods for “a direct simulation of a Turing machine by a tag system in polynomial time”（Cook 2009, PDF page 1, abstract, lines 23-24）。编译大小处写：`Using these two methods, the entire compilation algorithm in this section takes only polynomial time in the size of the Turing machine's initial configuration, and creates a Rule 110 initial state of polynomial size.`（Cook 2009, PDF page 3, §1.2, lines 152-159）。这里的 “TM initial configuration” 按原文是 Turing machine finite description plus its initial tape arrangement；Cook 在同段把 exponential-long tag rules/tape 的两个来源分别替换为 many new symbols 和 new states for writing the initial tape（Cook 2009, PDF page 3, §1.2, lines 152-157）。

### 1.2 Block decomposition

Cook 2009 Figure 1/2 给出实际 bit blocks。PDF 文本没有抽出每个 block 的逐 cell row string；因此每个 block 的 t=0 row cell count 需要视觉读图或从源图恢复，不能从可用 `pdftotext` 可靠抄出。可直接确认的数字如下。

| block | 用途 | 周期/行数 | 论文出处 |
|---|---|---:|---|
| `A` | left periodic region 的 pure ether spacer | 3 lines | Cook 2009, PDF page 4, Figure 1 caption, lines 242-246 |
| `B` | left periodic region 的 ossifier carrier；`BA13BA11BA12B` assembly 含 A4 ossifier | 3 lines | Cook 2009, PDF page 4, Figure 1 caption, lines 242-246；§1.5, lines 305-309 |
| `C` | central region t=0 seam anchor | non-periodic anchor | Cook 2009, PDF page 4, Figure 1 caption, lines 242-246 |
| `D` | moving data 邻接 glue；central tape `N -> ED`, `Y -> FD` | 30 lines | Cook 2009, PDF page 4, Figure 1 caption, lines 242-246；§1.4, lines 202-204 |
| `E` | moving data `N`, including seam `Ē` | 30 lines | Cook 2009, PDF page 4, Figure 1 caption, lines 242-246；§1.5, lines 310-311 |
| `F` | moving data `Y`, including seam `Ē` | 30 lines | Cook 2009, PDF page 4, Figure 1 caption, lines 242-246；§1.5, lines 310-311 |
| `G` | prepared leader | 30 lines | Cook 2009, PDF page 4, Figure 1 caption, lines 242-246；§1.5, lines 319-323 |
| `H` | primary component | 30 strings/phase rows stored by a program | Cook 2009, PDF page 5, Figure 2 caption, lines 277-282；§1.5, lines 316-318 |
| `I` | standard component, `II` encodes table-data `Y` | 30 strings/phase rows | Cook 2009, PDF page 5, Figure 2 caption, lines 277-282；§1.5, lines 316-318 |
| `J` | standard component with wider spacing, `IJ` encodes table-data `N` | 30 strings/phase rows | Cook 2009, PDF page 5, Figure 2 caption, lines 277-282；§1.5, lines 316-318 |
| `K` | raw leader | 30 strings/phase rows | Cook 2009, PDF page 5, Figure 2 caption, lines 277-282；§1.5, lines 319-323 |
| `L` | raw short leader for empty appendant | 30 strings/phase rows | Cook 2009, PDF page 5, Figure 2 caption, lines 277-282；§1.5, lines 319-323 |

Block-string recipes:

| region | recipe | 论文出处 |
|---|---|---|
| central tape | start with `C`; each `N` becomes `ED`; each `Y` becomes `FD`; final `D` becomes `G`; example `NNYN -> CEDEDFDEG` | Cook 2009, PDF page 4, §1.4, lines 202-204 |
| right periodic appendants | each appendant changes `Y -> II`, `N -> IJ`; first `I` becomes `KH`; empty appendant uses `L`; first appendant's initial `K` moves to the end; example `{YN, NYYN, /0, /0} -> HIIJKHJIIIIIJLLK` | Cook 2009, PDF page 6, §1.4, lines 286-288 |
| left periodic ossifiers | `[A]v B [A]13 B [A]11 B [A]12 B`, repeated three times before bit period begins | Cook 2009, PDF page 6, §1.4, lines 292-300 |
| `v` | `76*(total Ys in appendants) + 80*(total Ns in appendants) + 60*(nonempty appendants) + 43*(empty appendants)` | Cook 2009, PDF page 6, §1.4, lines 292-296 |

Figure spacing recipes:

| figure | exact spacing statement | 论文出处 |
|---|---|---|
| Figure 6 | `Ē` produces `C2` from `A4` only in construction case `Ē` is `up 5` from `A4`; `Ē` crosses `A4` iff it is `up 0`; consecutive `A4`s must be `up 5` from each other; every `Ē` is either invisible crossing all `A4`s or moving data ossified to `C2` | Cook 2009, PDF page 13, Figure 6 caption, lines 639-654 |
| Figure 7 | acceptor converts primary/standard components into moving data; rejector deletes components; measurements to/from clusters use closest glider touching the measured ether | Cook 2009, PDF page 14, Figure 7 caption, lines 693-700 |
| Figure 8 | invisibles from a prepared leader have alignment `k+5`; after moving data, prepared leader offset `k=0` gives `5`; after rejected invisibles, `k = 4+1+(2c-1)*5+2 = 10c+2`, and `c` multiple of 6 gives `k=2`, so invisibles have alignment `1` | Cook 2009, PDF page 15, Figure 8 caption, lines 759-769 |
| Figure 9 | raw leaders are placed `up 0` from previous component; if no previous components, raw leader is `up 0` from previous short leader; raw short leaders are `up +3` higher through the `E^n`s than raw regular leaders | Cook 2009, PDF page 16, Figure 9 caption, lines 808-814 |
| Figure 10 | first moving data after invisible, every invisible, and moving data after moving data have correct alignment to pass through tape data | Cook 2009, PDF page 17, Figure 10 caption, lines 860-866 |
| Figure 11 | leader preparation has total `⌢` distance mod 4 equal to `1 + 0 + 3 + (2c - 1)*(0 + 3) + 0 = 6c + 1 = 1` when `c` is multiple of 6 | Cook 2009, PDF page 18, Figure 11 caption, lines 931-933 |

Figure 5 baseline:

| figure | exact collision identity | 论文出处 |
|---|---|---|
| Figure 5(a) | In the unique crossing collision where an `Ē` crosses a `C2`, the regenerated `C2` is `⌢ 2` from the regenerated `Ē` modulo 4. | Cook 2009, PDF page 12, Figure 5 caption, lines 560-563 |
| Figure 5(b) | Two consecutive `Ē`s both cross a `C2` iff the `Ē`s are `⌢ 3` from each other; that spacing is preserved after the two collisions. | Cook 2009, PDF page 12, Figure 5 caption, lines 563-566 |
| Figure 5(c) | Consecutive `C2`s both cross an `Ē` iff they are `⌢ (3+3) = ⌢ 2` from each other; that spacing is preserved after the collisions. | Cook 2009, PDF page 12, Figure 5 caption, lines 567-570 |

### 1.3 Phase-exact emitter anchors

Cook 2009 Figures 6-11 and Cook 2004 Figure 12 give collision-level alignment anchors for the phase-exact emitters. The `pdftotext -layout` captions expose most formulas; 200 dpi `pdftoppm` PNGs make the small diagram numerals in Cook 2009 Figures 6-11 readable. Cook 2004 Figure 12 is a dense cellular-automaton picture, so the usable exact values there come from caption/body text rather than direct cell counting.

| figure | extracted data | implementation comparison |
|---|---|---|
| Cook 2009 Figure 6 | `Ē` produces `C2` from `A4` in the construction case only when `Ē` is `up 5` from `A4`; the resulting `C2` is distance `0` from the creating `Ē`; `Ē` crosses `A4` iff it is `up 0`; incoming `A4` is `up 5` from regenerated `Ē`; consecutive `A4`s are `up 5`; after an invisible `Ē`, `k=0` produces `C2` and `k=1` crosses; after moving data, `k=4` produces `C2` and `k=5` crosses (from caption and figure visual; PDF page 13, lines 639-654). | Closed by W30 in `cook_ossifier.c`: the phase-exact branch takes explicit input/action context, maps to `k=0/1/4/5`, and spaces consecutive `A4`s by 5 ether tiles. |
| Cook 2009 Figure 7 | Acceptor/rejector processing uses local measurement labels `(i) 0,0,3,5`, `(j) 0,2`, `(k) 0,4,3,5`, `(l) 0,2`; acceptor converts primary/standard components into moving data and rejector deletes components; cluster measurements use the closest glider touching the measured ether (from caption and figure visual; PDF page 14, lines 693-700). | Figure-level local measurement labels remain open; acceptor/rejector `A` products are closed by W26 through phase products in `cook_leader.c`. |
| Cook 2009 Figure 8 | Invisibles from a prepared leader have alignment `k+5`; after moving data, acceptor preparation gives `k=0` and invisible alignment `5`; after rejected invisibles, `k = 4+1+(2c-1)*5+2 = 10c+2`, and `c` multiple of 6 gives `k=2`, hence invisible alignment `1`; the diagram also shows local labels `3,2,k`, `0,0,k`, and `4,1,5,2,k` with the `2c-1` span (from caption and figure visual; PDF page 15, lines 759-769). | Closed by W30 in `cook_leader.c`: prepared leader emission computes `k+5` alignment from context, including `k=0` after moving data and normalized `k=2` for rejected invisibles with `c` a multiple of 6. |
| Cook 2009 Figure 9 | Raw leaders are `up 0` from the previous component; with no previous component, raw leader is `up 0` from the previous short leader; raw leaders after short leaders give prepared leaders with `k=2`; raw short leaders are `up +3` higher through the `E^n`s than raw regular leaders. Diagram labels are `(p) 3,3`, `(q) 0,0`, `(r) 0,0,0,2,k=2` (from caption and figure visual; PDF page 16, lines 808-814). | Raw regular/short leader selection and the `up +3` short-leader placement rule are closed by W26 in `cook_leader.c`; prepared leader `k=2` propagation remains open. |
| Cook 2009 Figure 10 | Moving data and invisibles are aligned to pass through tape data; first moving data after an invisible uses the Figure 5(b) relation; every invisible uses Figure 5(a,c); moving data after moving data uses Figure 5(b). Diagram labels are `(s) 0,1,2`, `(t) 2,1`, `(u) 0,1,2` (from caption and figure visual; PDF page 17, lines 860-866). | Closed by W35 in `cook_collision_identity.c`, `cook_data_block.c`, and `cook_leader.c`: Figure 5(a/b/c) is encoded as a shared contract; tape `C2` spacings are checked as `2 mod 4`, and moving-data `Ē` pass-through spacing is checked as `3 mod 4`. |
| Cook 2009 Figure 11 | Prepared leader placement uses `(v) 0,1`, `(w) 2,3`, `(x) 1,0`, and `(y) 1,0,3,0,3,0` with a `2c-1` span; because `c` is a multiple of 6, the total distance mod 4 is `1 + 0 + 3 + (2c - 1)*(0 + 3) + 0 = 6c + 1 = 1` (from caption and figure visual; PDF page 18, lines 931-933). | Closed by W33 in `cook_leader.c`: prepared leader placement stores `(v,w,x,y)`, requires `c` to be a multiple of 6, computes the `2c-1` span, and checks total distance `1 mod 4`. |
| Cook 2004 Figure 12 | Leader/tape interaction uses eight `E` gliders, mostly `Ē`, hitting four vertical `C2`s; tape `N` produces rejector `A3`; tape `Y` produces acceptor `A4 A1 A`; both cases emit two invisible `Ē`s to the left; the first `Ē` reacts with four `C2`s, emits two `A`s, and becomes an invisible `Ē`; the center-`C2` spacing difference changes the emitted-`A` timing (from caption/body; PDF page 25-26, lines 1090-1112). Body text gives tape `Y = C2 18 C2 18 C2 14 C2` and tape `N = C2 18 C2 10 C2 14 C2` (PDF page 30, lines 1252-1257). | Figure 12 `N={18,10,14}` and `A3`/`A4 A1 A` phase products are closed by W26 in `cook_data_block.c`, `cook_decode.c`, and `cook_leader.c`; the two emitted invisible `Ē`s and left-side four-`C2` reaction timing remain open. |

Ossifier semantics: Cook 2004 says moving data uses `Ē`, tape data uses `C2`, and ossifiers use `A4` (Cook 2004, PDF page 24, §4, lines 1075-1079). Four `A4`s convert four `Ē`s of a moving-data character into four `C2`s of a tape-data character (Cook 2004, PDF page 26, §4, lines 1147-1155). Consecutive ossifiers must have gap form `A4 6k+5 A4` with `k` large enough for required spacing (Cook 2004, PDF page 29, §4, lines 1224-1227).

Data block semantics: tape `Y` is represented by `C2 18 C2 18 C2 14 C2`; tape `N` is represented by `C2 18 C2 10 C2 14 C2` (Cook 2004, §4, lines 1252-1253). Moving data inverts the middle spacing: the central `C2` gap `18` vs `10` is produced by changing central `Ē` spacing by `8A` (Cook 2004, §4, lines 1252-1257). Cook 2009 encodes central tape symbols as `N -> ED`, `Y -> FD`, with final `D -> G` (Cook 2009, PDF page 4, §1.4, lines 202-204).

## Part 2: Phase catalog

### 2.1 Glider properties and phase rows

Martinez 2007 Table 2 gives period/shift through the speed column; the table below records the period denominator and displacement numerator used for every Appendix row in the same glider group (Martinez 2007, PDF page 5, §3, Table 2, lines 184-205).

| group | period | displacement per period | width |
|---|---:|---:|---:|
| ether `er` | 3 | `+2` | 14 |
| ether `el` | 2 | `-1` | 14 |
| `A` | 3 | `+2` | 6 |
| `B` | 4 | `-2` | 8 |
| `B̄_n` | 12 | `-6` | 22 |
| `B̂_n` | 12 | `-6` | 39 |
| `C1` | 7 | `0` | 9-23 |
| `C2` | 7 | `0` | 17 |
| `C3` | 7 | `0` | 11 |
| `D1` | 10 | `+2` | 11-25 |
| `D2` | 10 | `+2` | 19 |
| `E_n` | 15 | `-4` | 19 |
| `Ē` | 30 | `-8` | 21 |
| `F` | 36 | `-4` | 15-29 |
| `G_n` | 42 | `-14` | 24-38 |
| `H` | 92 | `-18` | 39-53 |
| glider gun | 77 | `-20` | 27-55 |

Appendix A presents the finite subset `Ph1` of regular expressions for known Rule 110 gliders (Martinez 2007, PDF page 29, Appendix A, lines 1317-1325). The following list keeps Appendix order. Entries marked `[CATALOG GAP]` are present in Martinez 2007 but absent from `rule110/encoder/glider_phases.c` lines 15-208.

| entry | phase strings | source |
|---|---|---|
| `e` | f1=`11111000100110` | p29, A.1, lines 1352-1352 |
| `A` | f1=`111110`; f2=`11111000111000100110`; f3=`11111000100110100110`; f4=`111110` | p30, A.2, lines 1363-1366 |
| `B` | f1=`11111010`; f2=`11111000`; f3=`1111100010011000100110`; f4=`11100110` | p30, A.3, lines 1369-1372 |
| `B̄(A)` | f1=`1111100010110111100110`; f2=`111110001001111111001011111000100110`; f3=`111110001001101100000101111000100110`; f4=`1111110000111100100110` | p30, A.4, lines 1375-1378 |
| `B̄(B)` | f1=`1111100001000110010110`; f2=`111110001000110011101111111000100110`; f3=`111110001001100111011011100000100110`; f4=`1110110111111010000110` | p30, A.4, lines 1380-1383 |
| `B̄(C)` | f1=`1111101111110000111000`; f2=`111110001110000100011010011000100110`; f3=`111110001001101000110011111011100110`; f4=`1111100111011000111010` | p30, A.4, lines 1385-1388 |
| `B̂(A)` | f1=`111110001011011110011001111111000100110`; f2=`111110001001111111001011101100000100110`; f3=`111110001001101100000101111011110000110`; f4=`1111110000111100111001000` | p30, A.5, lines 1391-1394 [CATALOG GAP] |
| `B̂(B)` | f1=`111110000100011001011010110011000100110`; f2=`111110001000110011101111111111011100110`; f3=`111110001001100111011011100000000111010`; f4=`1110110111111010000000110` | p30, A.5, lines 1396-1399 [CATALOG GAP] |
| `B̂(C)` | f1=`111110111111000011100000011111000100110`; f2=`111110001110000100011010000011000100110`; f3=`111110001001101000110011111000011100110`; f4=`1111100111011000100011010` | p30, A.5, lines 1401-1404 [CATALOG GAP] |
| `C1(A)` | f1=`111110000`; f2=`11111000100011000100110`; f3=`11111000100110011100110`; f4=`111011010` | p31, A.6, lines 1412-1415 |
| `C1(B)` | f1=`11111011111111000100110`; f2=`11111000111000000100110`; f3=`11111000100110100000110`; f4=`11111011111111000100110` | p31, A.6, lines 1417-1420 |
| `C2(A)` | f1=`11111000000100110`; f2=`11111000100000110`; f3=`11111000100110000`; f4=`11100011000100110` | p31, A.7, lines 1423-1426 |
| `C2(B)` | f1=`11111010011100110`; f2=`11111000111011010`; f3=`1111100010011011111111000100110`; f4=`11111010011100110` | p31, A.7, lines 1428-1431 |
| `C3(A)` | f1=`11111011010`; f2=`1111100011111111000100110`; f3=`1111100010011000000100110`; f4=`11100000110` | p31, A.8, lines 1434-1437 |
| `C3(B)` | f1=`11111010000`; f2=`1111100011100011000100110`; f3=`1111100010011010011100110`; f4=`11111010000` | p31, A.8, lines 1439-1442 |
| `D1(A)` | f1=`11111000010`; f2=`1111100010001111000100110`; f3=`1111100010011001100100110`; f4=`11101110110` | p31, A.9, lines 1445-1448 |
| `D1(B)` | f1=`1111101110111111000100110`; f2=`1111100011101110000100110`; f3=`1111100010011011101000110`; f4=`11111011100` | p31, A.9, lines 1450-1453 |
| `D1(C)` | f1=`11111011100`; f2=`1111100011101011000100110`; f3=`1111100010011011111100110`; f4=`11111000010` | p31-p32, A.9, lines 1455-1463 |
| `D2(A)` | f1=`1111101011000100110`; f2=`1111100011111100110`; f3=`1111100010011000010`; f4=`1110001111000100110` | p32, A.10, lines 1466-1469 |
| `D2(B)` | f1=`1111101001100100110`; f2=`1111100011101110110`; f3=`111110001001101110111111000100110`; f4=`1111101110000100110` | p32, A.10, lines 1471-1474 |
| `D2(C)` | f1=`1111101110000100110`; f2=`1111100011101000110`; f3=`1111100010011011100`; f4=`1111101011000100110` | p32, A.10, lines 1476-1479 |
| `E(A)` | f1=`1111100000000100110`; f2=`1111100010000000110`; f3=`1111100010011000000`; f4=`1110000011000100110` | p32, A.11, lines 1482-1485 [CATALOG GAP] |
| `E(B)` | f1=`1111101000011100110`; f2=`1111100011100011010`; f3=`111110001001101001111111000100110`; f4=`1111101100000100110` | p32, A.11, lines 1487-1490 [CATALOG GAP] |
| `E(C)` | f1=`1111101100000100110`; f2=`1111100011110000110`; f3=`1111100010011001000`; f4=`1110110011000100110` | p32, A.11, lines 1492-1495 [CATALOG GAP] |
| `E(D)` | f1=`1111101111011100110`; f2=`1111100011100111010`; f3=`1111100010011010110`; f4=`1111111111000100110` | p32, A.11, lines 1497-1500 [CATALOG GAP] |
| `Ē(A)` | f1=`111110000100011111010`; f2=`111110001000110011000`; f3=`11111000100110011101110011000100110`; f4=`111011011101011100110` | p32, A.12, lines 1503-1506 |
| `Ē(B)` | f1=`111110111111011111010`; f2=`111110001110000111000`; f3=`11111000100110100011010011000100110`; f4=`111110011111011100110` | p33, A.12, lines 1513-1516 |
| `Ē(C)` | f1=`111110001011000111010`; f2=`111110001001111100110`; f3=`11111000100110110001011111000100110`; f4=`111111001111000100110` | p33, A.12, lines 1518-1521 |
| `Ē(D)` | f1=`111110000101100100110`; f2=`111110001000111110110`; f3=`11111000100110011000111111000100110`; f4=`111011100110000100110` | p33, A.12, lines 1523-1526 |
| `Ē(E)` | f1=`111110111010111000110`; f2=`111110001110111110100`; f3=`11111000100110111000111011000100110`; f4=`111110100110111100110` | p33, A.12, lines 1528-1531 |
| `Ē(F)` | f1=`111110100110111100110`; f2=`111110001110111110010`; f3=`11111000100110111000101111000100110`; f4=`111110100111100100110` | p33, A.12, lines 1533-1536 |
| `Ē(G)` | f1=`111110100111100100110`; f2=`111110001110110010110`; f3=`11111000100110111101111111000100110`; f4=`111110011100000100110` | p33, A.12, lines 1538-1541 |
| `Ē(H)` | f1=`111110001011010000110`; f2=`111110001001111111000`; f3=`11111000100110110000010011000100110`; f4=`111111000011011100110` | p33, A.12, lines 1543-1546 |
| `F(A)` | f1=`111110001011010`; f2=`11111000100111111111000100110`; f3=`11111000100110110000000100110`; f4=`111111000000110` | p33, A.13, lines 1549-1552 |
| `F(B)` | f1=`111110000100000`; f2=`11111000100011000011000100110`; f3=`11111000100110011100011100110`; f4=`111011010011010` | p33, A.13, lines 1554-1557 |
| `F(C)` | f1=`11111011111101111111000100110`; f2=`11111000111000011100000100110`; f3=`11111000100110100011010000110`; f4=`111110011111000` | p33-p34, A.13, lines 1559-1566 |
| `F(D)` | f1=`11111000101100010011000100110`; f2=`11111000100111110011011100110`; f3=`11111000100110110001011111010`; f4=`111111001111000` | p34, A.13, lines 1568-1571 |
| `F(E)` | f1=`11111000010110010011000100110`; f2=`11111000100011111011011100110`; f3=`11111000100110011000111111010`; f4=`111011100110000` | p34, A.13, lines 1573-1576 |
| `F(F)` | f1=`11111011101011100011000100110`; f2=`11111000111011111010011100110`; f3=`11111000100110111000111011010`; f4=`11111010011011111111000100110` | p34, A.13, lines 1578-1581 |
| `F(G)` | f1=`11111010011011111111000100110`; f2=`11111000111011111000000100110`; f3=`11111000100110111000100000110`; f4=`111110100110000` | p34, A.13, lines 1583-1586 |
| `F(H)` | f1=`111110100110000`; f2=`11111000111011100011000100110`; f3=`11111000100110111010011100110`; f4=`111110111011010` | p34, A.13, lines 1588-1591 |
| `F(A2)` | f1=`111110111011010`; f2=`11111000111011111111000100110`; f3=`11111000100110111000000100110`; f4=`111110100000110` | p34, A.13, lines 1593-1596 |
| `F(B2)` | f1=`111110100000110`; f2=`111110001110000`; f3=`11111000100110100011000100110`; f4=`111110011100110` | p34, A.13, lines 1598-1601 |
| `G(A)` | f1=`111110100111110011100110`; f2=`111110001110110001011010`; f3=`11111000100110111100111111111000100110`; f4=`111110010110000000100110` | p34, A.14, lines 1604-1607 |
| `G(B)` | f1=`111110001011111000000110`; f2=`111110001001111000100000`; f3=`11111000100110110010011000011000100110`; f4=`111111011011100011100110` | p34, A.14, lines 1609-1612 |
| `G(C)` | f1=`111110000111111010011010`; f2=`11111000100011000011101111111000100110`; f3=`11111000100110011100011011100000100110`; f4=`111011010011111010000110` | p35, A.14, lines 1619-1622 |
| `G(D)` | f1=`111110111111011000111000`; f2=`11111000111000011110011010011000100110`; f3=`11111000100110100011001011111011100110`; f4=`111110011101111000111010` | p35, A.14, lines 1624-1627 |
| `G(E)` | f1=`111110001011011100100110`; f2=`11111000100111111101011011111000100110`; f3=`11111000100110110000011111111000100110`; f4=`111111000011000000100110` | p35, A.14, lines 1629-1632 |
| `G(F)` | f1=`111110000100011100000110`; f2=`11111000100011001101000011111000100110`; f3=`11111000100110011101111100011000100110`; f4=`111011011100010011100110` | p35, A.14, lines 1634-1637 |
| `G(G)` | f1=`111110111111010011011010`; f2=`11111000111000011101111111111000100110`; f3=`11111000100110100011011100000000100110`; f4=`111110011111010000000110` | p35, A.14, lines 1639-1642 |
| `G(H)` | f1=`111110001011000111000000`; f2=`11111000100111110011010000011000100110`; f3=`11111000100110110001011111000011100110`; f4=`111111001111000100011010` | p35, A.14, lines 1644-1647 |
| `G(A2)` | f1=`11111000010110010011001111111000100110`; f2=`11111000100011111011011101100000100110`; f3=`11111000100110011000111111011110000110`; f4=`111011100110000111001000` | p35, A.14, lines 1649-1652 |
| `G(B2)` | f1=`11111011101011100011010110011000100110`; f2=`11111000111011111010011111111011100110`; f3=`11111000100110111000111011000000111010`; f4=`111110100110111100000110` | p35, A.14, lines 1654-1657 |
| `G(C2)` | f1=`111110100110111100000110`; f2=`11111000111011111001000011111000100110`; f3=`11111000100110111000101100011000100110`; f4=`111110100111110011100110` | p35, A.14, lines 1659-1662 |
| `H(A)` | f1=`11111000101100000000111110001001101001111111000100110`; f2=`11111000100111110000000110001001101111101100000100110`; f3=`11111000100110110001000000111001101111100011110000110`; f4=`111111001100000110101111100010011001000` | p35-p36, A.15, lines 1665-1672 |
| `H(B)` | f1=`11111000010111000011111110001001101110110011000100110`; f2=`11111000100011110100011000001001101111101111011100110`; f3=`11111000100110011001110011100001101111100011100111010`; f4=`111011101101011010001111100010011010110` | p36, A.15, lines 1674-1677 [CATALOG GAP] |
| `H(C)` | f1=`11111011101111111111100110001001101111111111000100110`; f2=`11111000111011100000000010111001101111100000000100110`; f3=`11111000100110111010000000011110101111100010000000110`; f4=`111110111000000011001111100010011000000` | p36, A.15, lines 1679-1682 [CATALOG GAP] |
| `H(D)` | f1=`111110111000000011001111100010011000000`; f2=`11111000111010000001110110001001101110000011000100110`; f3=`11111000100110111000001101111001101111101000011100110`; f4=`111110100001111100101111100011100011010` | p36, A.15, lines 1684-1687 [CATALOG GAP] |
| `H(E)` | f1=`111110100001111100101111100011100011010`; f2=`11111000111000110001011110001001101001111111000100110`; f3=`11111000100110100111001111001001101111101100000100110`; f4=`111110110101100101101111100011110000110` | p36, A.15, lines 1689-1692 [CATALOG GAP] |
| `H(F)` | f1=`111110110101100101101111100011110000110`; f2=`111110001111111110111111100010011001000`; f3=`11111000100110000000111000001001101110110011000100110`; f4=`111000000110100001101111101111011100110` | p36, A.15, lines 1694-1697 [CATALOG GAP] |
| `H(G)` | f1=`111110100000111110001111100011100111010`; f2=`111110001110000110001001100010011010110`; f3=`11111000100110100011100110111001101111111111000100110`; f4=`111110011010111110101111100000000100110` | p36, A.15, lines 1699-1702 [CATALOG GAP] |
| `H(H)` | f1=`111110001011111110001111100010000000110`; f2=`111110001001111000001001100010011000000`; f3=`11111000100110110010000110111001101110000011000100110`; f4=`111111011000111110101111101000011100110` | p36, A.15, lines 1704-1707 [CATALOG GAP] |
| `H(A2)` | f1=`111110000111100110001111100011100011010`; f2=`11111000100011001011100110001001101001111111000100110`; f3=`11111000100110011101111010111001101111101100000100110`; f4=`111011011100111110101111100011110000110` | p36, A.15, lines 1709-1712 [CATALOG GAP] |
| `H(B2)` | f1=`111110111111010110001111100010011001000`; f2=`11111000111000011111100110001001101110110011000100110`; f3=`11111000100110100011000010111001101111101111011100110`; f4=`111110011100011110101111100011100111010` | p36, A.15, lines 1714-1717 [CATALOG GAP] |
| `H(C2)` | f1=`111110001011010011001111100010011010110`; f2=`11111000100111111101110110001001101111111111000100110`; f3=`11111000100110110000011101111001101111100000000100110`; f4=`111111000011011100101111100010000000110` | p36-p37, A.15, lines 1719-1726 [CATALOG GAP] |
| `H(D2)` | f1=`111110000100011111010111100010011000000`; f2=`11111000100011001100011111001001101110000011000100110`; f3=`11111000100110011101110011000101101111101000011100110`; f4=`111011011101011100111111100011100011010` | p37, A.15, lines 1728-1731 [CATALOG GAP] |
| `H(E2)` | f1=`11111011111101111101011000001001101001111111000100110`; f2=`11111000111000011100011111100001101111101100000100110`; f3=`11111000100110100011010011000010001111100011110000110`; f4=`111110011111011100011001100010011001000` | p37, A.15, lines 1733-1736 [CATALOG GAP] |
| `H(F2)` | f1=`11111000101100011101001110111001101110110011000100110`; f2=`11111000100111110011011101101110101111101111011100110`; f3=`11111000100110110001011111011111101111100011100111010`; f4=`111111001111000111000011100010011010110` | p37, A.15, lines 1738-1741 [CATALOG GAP] |
| `H(G2)` | f1=`11111000010110010011010001101001101111111111000100110`; f2=`11111000100011111011011111001111101111100000000100110`; f3=`11111000100110011000111111000101100011100010000000110`; f4=`111011100110000100111110011010011000000` | p37, A.15, lines 1743-1746 [CATALOG GAP] |
| `H(H2)` | f1=`11111011101011100011011000101111101110000011000100110`; f2=`11111000111011111010011111100111100011101000011100110`; f3=`11111000100110111000111011000010110010011011100011010`; f4=`11111010011011110001111101101111101001111111000100110` | p37, A.15, lines 1748-1751 [CATALOG GAP] |
| `H(A3)` | f1=`11111010011011110001111101101111101001111111000100110`; f2=`11111000111011111001001100011111100011101100000100110`; f3=`11111000100110111000101101110011000010011011110000110`; f4=`111110100111111101011100011011111001000` | p37, A.15, lines 1753-1756 [CATALOG GAP] |
| `H(B3)` | f1=`111110100111111101011100011011111001000`; f2=`11111000111011000001111101001111100010110011000100110`; f3=`11111000100110111100001100011101100010011111011100110`; f4=`111110010001110011011110011011000111010` | p37, A.15, lines 1758-1761 [CATALOG GAP] |
| `H(C3)` | f1=`111110001011001101011111001011111100110`; f2=`11111000100111110111111100010111100001011111000100110`; f3=`11111000100110110001110000010011110010001111000100110`; f4=`111111001101000011011001011001100100110` | p37, A.15, lines 1763-1766 [CATALOG GAP] |
| `H(D3)` | f1=`111110000101111100011111101111101110110`; f2=`11111000100011110001001100001110001110111111000100110`; f3=`11111000100110011001001101110001101001101110000100110`; f4=`111011101101111101001111101111101000110` | p37, A.15, lines 1768-1771 [CATALOG GAP] |
| `H(E3)` | f1=`111110111011111100011101100011100011100`; f2=`11111000111011100001001101111001101001101011000100110`; f3=`11111000100110111010001101111100101111101111111100110`; f4=`111110111001111100010111100011100000010` | p37-p38, A.15, lines 1773-1780 [CATALOG GAP] |
| `H(F3)` | f1=`111110111001111100010111100011100000010`; f2=`11111000111010110001001111001001101000001111000100110`; f3=`11111000100110111111001101100101101111100001100100110`; f4=`111110000101111110111111100010001110110` | p38, A.15, lines 1782-1785 [CATALOG GAP] |
| `H(G3)` | f1=`111110000101111110111111100010001110110`; f2=`11111000100011110000111000001001100110111111000100110`; f3=`11111000100110011001000110100001101110111110000100110`; f4=`111011101100111110001111101110001000110` | p38, A.15, lines 1787-1790 [CATALOG GAP] |
| `H(H3)` | f1=`111110111011110110001001100011101001100`; f2=`11111000111011100111100110111001101110111011000100110`; f3=`11111000100110111010110010111110101111101110111100110`; f4=`111110111111011110001111100011101110010` | p38, A.15, lines 1792-1795 [CATALOG GAP] |
| `H(A4)` | f1=`111110111111011110001111100011101110010`; f2=`11111000111000011100100110001001101110101111000100110`; f3=`11111000100110100011010110111001101111101111100100110`; f4=`111110011111111110101111100011100010110` | p38, A.15, lines 1797-1800 [CATALOG GAP] |
| `Gun(A)` | f1=`11111010110011101001100101111100000100110`; f2=`11111000111111011011101110111100010000110`; f3=`11111000100110000111111011101110010011000`; f4=`11100011000011101110101101110011000100110` | p38, A.16, lines 1803-1806 |
| `Gun(B)` | f1=`11111010011100011011101111111101011100110`; f2=`11111000111011010011111011100000011111010`; f3=`11111000100110111111011000111010000011000`; f4=`11111000011110011011100001110011000100110` | p38, A.16, lines 1808-1811 [CATALOG GAP] |
| `Gun(C)` | f1=`11111000011110011011100001110011000100110`; f2=`11111000100011001011111010001101011100110`; f3=`11111000100110011101111000111001111111010`; f4=`111011011100100110101100000` | p38, A.16, lines 1813-1816 [CATALOG GAP] |
| `Gun(D)` | f1=`11111011111101011011111111000011000100110`; f2=`11111000111000011111111000000100011100110`; f3=`11111000100110100011000000100000110011010`; f4=`11111001110000011000011101111111000100110` | p38, A.16, lines 1818-1821 [CATALOG GAP] |
| `Gun(E)` | f1=`11111000101101000011100011011100000100110`; f2=`11111000100111111100011010011111010000110`; f3=`11111000100110110000010011111011000111000`; f4=`11111100001101100011110011010011000100110` | p38, A.16, lines 1823-1826 [CATALOG GAP] |
| `Gun(F)` | f1=`11111000010001111110011001011111011100110`; f2=`11111000100011001100001011101111000111010`; f3=`11111000100110011101110001111011100100110`; f4=`11101101110100110011101011011111000100110` | p39, A.16, lines 1833-1836 [CATALOG GAP] |
| `Gun(G)` | f1=`11111011111101110111011011111111000100110`; f2=`11111000111000011101110111111000000100110`; f3=`11111000100110100011011101110000100000110`; f4=`11111001111101110100011000011111000100110` | p39, A.16, lines 1838-1841 [CATALOG GAP] |
| `Gun(H)` | f1=`11111000101100011101110011100011000100110`; f2=`11111000100111110011011101011010011100110`; f3=`11111000100110110001011111011111111011010`; f4=`11111100111100011100000011111111000100110` | p39, A.16, lines 1843-1846 [CATALOG GAP] |
| `Gun(A2)` | f1=`11111000010110010011010000011000000100110`; f2=`11111000100011111011011111000011100000110`; f3=`11111000100110011000111111000100011010000`; f4=`11101110011000010011001111100011000100110` | p39, A.16, lines 1848-1851 [CATALOG GAP] |
| `Gun(B2)` | f1=`11111011101011100011011101100010011100110`; f2=`11111000111011111010011111011110011011010`; f3=`1111100010011011100011101100011100101111111111000100110`; f4=`11111010011011110011010111100000000100110` | p39, A.16, lines 1853-1856 [CATALOG GAP] |
| `Gun(C2)` | f1=`11111010011011110011010111100000000100110`; f2=`11111000111011111001011111110010000000110`; f3=`11111000100110111000101111000001011000000`; f4=`11111010011110010000111110000011000100110` | p39, A.16, lines 1858-1861 [CATALOG GAP] |
| `Gun(D2)` | f1=`11111010011110010000111110000011000100110`; f2=`11111000111011001011000110001000011100110`; f3=`11111000100110111101111100111001100011010`; f4=`11111001110001011010111001111111000100110` | p39, A.16, lines 1863-1866 [CATALOG GAP] |
| `Gun(E2)` | f1=`11111000101101001111111110101100000100110`; f2=`11111000100111111101100000001111110000110`; f3=`11111000100110110000011110000001100001000`; f4=`11111100001100100000111000110011000100110` | p39, A.16, lines 1868-1871 [CATALOG GAP] |
| `Gun(F2)` | f1=`11111000010001110110000110100111011100110`; f2=`11111000100011001101111000111110110111010`; f3=`11111000100110011101111100100110001111110`; f4=`11101101110001011011100110000111000100110` | p39, A.16, lines 1873-1876 [CATALOG GAP] |
| `Gun(G2)` | f1=`11111011111101001111111010111000110100110`; f2=`11111000111000011101100000111110100111110`; f3=`1111100010011010001101111000011000111011000111000100110`; f4=`11111001111100100011100110111100110100110` | p39, A.16, lines 1878-1881 [CATALOG GAP] |
| `Gun(H2)` | f1=`11111000101100010110011010111110010`; f2=`1111100010011111001111101111111000101111000100110`; f3=`1111100010011011000101100011100000100111100100110`; f4=`11111100111110011010000110110010110` | p40, A.16, lines 1887-1890 [CATALOG GAP] |
| `Gun(A3)` | f1=`1111100001011000101111100011111101111111000100110`; f2=`1111100010001111100111100010011000011100000100110`; f3=`1111100010011001100010110010011011100011010000110`; f4=`11101110011111011011111010011111000` | p40, A.16, lines 1892-1895 [CATALOG GAP] |
| `Gun(B3)` | f1=`1111101110101100011111100011101100010011000100110`; f2=`1111100011101111110011000010011011110011011100110`; f3=`1111100010011011100001011100011011111001011111010`; f4=`11111010001111010011111000101111000` | p40, A.16, lines 1897-1900 [CATALOG GAP] |
| `Gun(C3)` | f1=`11111010001111010011111000101111000`; f2=`1111100011100110011101100010011110010011000100110`; f3=`1111100010011010111011011110011011001011011100110`; f4=`11111110111111001011111101111111010` | p40, A.16, lines 1902-1905 [CATALOG GAP] |
| `Gun(D3)` | f1=`11111000001110000101111000011100000`; f2=`1111100010000110100011110010001101000011000100110`; f3=`1111100010011000111110011001011001111100011100110`; f4=`11100110001011101111101100010011010` | p40, A.16, lines 1907-1910 [CATALOG GAP] |
| `Gun(E3)` | f1=`1111101011100111101110001111001101111111000100110` | p40, A.16, lines 1912-1912 [CATALOG GAP] |

Coverage arithmetic from `rule110/encoder/glider_phases.c` versus Martinez 2007 Appendix A: 193 project records, 394 parsed Appendix keys, 201 missing keys. Missing by group: `H=96`, `Gun=77`, `E=16`, `B̂=12`.

### 2.2 Neighbor semantics

Martinez’s notation is `#1(#2, f_i_1)` where `#1` is the localization/glider and `#2` is the phase when period is greater than four; `f_i` is the phase and the second subscript selects the master set of regular expressions (Martinez 2012, PDF page 9, §3.1, lines 378-391; same notation originates in Martinez 2007, PDF page 18, §4.4, lines 814-819). In Appendix A, the parenthesized letter before `f_i_1` acts as the adjacent ether/glider context used to cut a finite regular-expression row from a larger periodic tiling; this is why `B̄(A,f1_1)`, `B̄(B,f1_1)`, and `B̄(C,f1_1)` are different strings (Martinez 2007, PDF page 30, Appendix A.4, lines 1345-1359).

The phase sets are arranged as four levels: `Ph1 -> {f1_1,f2_1,f3_1,f4_1}`, `Ph2 -> {f1_2,...}`, `Ph3 -> {f1_3,...}`, `Ph4 -> {f1_4,...}` (Martinez 2007, PDF page 18, Table 6, lines 802-807). Appendix A lists `Ph1` only (Martinez 2007, PDF page 29, Appendix A, lines 1317-1321). Martinez says phases represent finite regular-expression sequences in the de Bruijn diagram, and a phase alignment determines a set of regular expressions for initial conditions (Martinez 2007, PDF page 18, §4.4, lines 771-782).

## Part 3: Collision and soliton table

### 3.1 Martinez 2012 Table 1 solitonic `F -> B` rows

Table 1 is not a collision table; it is the mobile self-localization property table (Martinez 2012, PDF page 8, §3.1, lines 366-375). The `F -> B` solitonic rows before Table 2 are:

| row | result | project status |
|---|---|---|
| `Soliton 4: F(A,f1_1)-3e-B(f4_1) -> {B,F}` | printed as `ö 8B, F<` | present at `rule110/encoder/cook_collisions.c` line 32 |

Source: Martinez 2012, PDF page 9, §3.1, line 403.

### 3.2 Martinez 2012 Table 2 rows

PDF OCR on Table 2 page 127 loses the overline: the two column headers both appear as `Collisions F Ø B`, while the caption says relation between `B`, `B`, and `F`. Visual reading is required to distinguish `B̄` in the left column from `B` in the right column. The rows below follow the printed row order in `pdftotext`; overline assignment follows the table layout and project naming.

| Table 2 row | outcome | project comparison |
|---|---|---|
| `F(A,f1_1)-e-B̄(A,f1_1)` | `{A, B, B̄, F}` | matches `cook_collisions.c` line 47 |
| `F(A,f1_1)-e-B(f1_1)` | `{B̄, F} *` | matches line 58 |
| `F(A,f1_1)-e-B̄(B,f1_1)` | `{A, 2 C3, C1}` | matches line 48 |
| `F(G,f1_1)-e-B(f1_1)` | `{B̄, F} *` | matches line 59 |
| `F(A,f1_1)-e-B̄(C,f1_1)` | `{A, C2}` | matches line 49 |
| `F(H,f1_1)-e-B(f1_1)` | `{D2, A²}` | matches line 60 |
| `F(G,f1_1)-e-B̄(A,f1_1)` | `{C2, A²}` | matches line 50 |
| `F(A2)-e-B` | `{B, F} (soliton)` | project has `F(A2)`/`B`, line 61 |
| `F(G,f1_1)-e-B̄(B,f1_1)` | `{A, A³, A, Ē}` | project stores `{A, A^3, A, Ebar}`, line 51 |
| `F(G,f1_1)-e-B̄(C,f1_1)` | `{B, F} *` | matches line 52 |
| `F(H,f1_1)-e-B̄(A,f1_1)` | `{A, C2}` | matches line 53 |
| `F(H,f1_1)-e-B̄(B,f1_1)` | `{Ē, A⁵}` | matches line 54; this is `A⁵`, not `A³` |
| `F(H,f1_1)-e-B̄(C,f1_1)` | `{Ē, A⁵}` | matches line 55; this is `A⁵`, not `A³` |
| `F(A2,f1_1)-e-B̄(A,f1_1)` | `{C1}` | matches line 56 |
| `F(A2,f1_1)-e-B̄(B,f1_1)` | `{A, B³, Ē}` | matches line 57 |

Source: Martinez 2012, PDF page 11 / printed page 127, Table 2, lines 485-507. The exact `A5` text is visible at lines 498 and 500; OCR does not preserve superscript formatting.

### 3.3 Soliton consistency

Martinez defines a soliton informally as two solitary waves colliding and emerging “with the same shape and velocity” (Martinez 2012, PDF page 2, Introduction, lines 53-55). Section 3 says a soliton preserves form and speed after interacting with another wave or obstacle, with phase and position affected by the collision (Martinez 2012, PDF page 5, §3, lines 228-234). For project semantics:

| category | operational meaning | source |
|---|---|---|
| soliton | both participating localizations are present after collision with same type and speed; phase/position may change | Martinez 2012, PDF page 2, lines 53-55; page 5, lines 230-234 |
| passthrough | gliders cross while preserving the relevant data spacing; Cook uses this for `Ē` crossing `C2` and `A4` crossing `Ē` | Cook 2004, lines 806-813, 829-848; Cook 2009 Figure 6 caption, lines 645-650 |
| annihilation | products are absent or deleted; in Cook construction rejector deletes table components | Cook 2004, lines 442-448 and 1138-1143; Cook 2009 Figure 7 caption, lines 693-696 |

## Part 4: Detection algorithm

### 4.1 What the papers describe

Martinez 2007 is not a detector implementation paper. It constructs regular expressions for glider phases using de Bruijn diagrams and tile alignments. It says the sequences are extracted from de Bruijn diagrams and tiles (Martinez 2007, PDF page 1, abstract, lines 32-35), phases “indicate with precision both the position and the exact” glider coding (PDF page 4, §3, lines 168-175), and Appendix A gives finite regular-expression rows for known gliders (PDF page 29, Appendix A, lines 1317-1321). The closest algorithmic detector implied by the paper is regular-expression/phase matching, not connected-component diffing against ether.

Cook 2004 uses visual glider identification and relative-distance bookkeeping. It explicitly notes humans visually identify objects in two-dimensional evolutions (Cook 2004, lines 543-565), then defines `Ē` diagonal and vertical measurement rows/columns for phase-accurate collision alignment (Cook 2004, Figure 7 lines 719-727; Figure 8 lines 766-790). That is frame/geometry tracking for construction proof, not a one-row string scanner.

### 4.2 What `rule110` uses

`rule110/encoder/cook_decode.c` is phase pattern matching plus a phase-ledger fallback. It matches raw bit strings with `row_matches_bits` (lines 31-44), scans for `C2(A, phase)` strings via `glider_phase("C2","A",phase)` (lines 194-201), collects all C2 hits by row scan (lines 204-221), and classifies packets by exact spacing arrays `Y_SPACINGS={18,18,14}` and `N_SPACINGS={18,10,14}` (lines 253-258). This corresponds to Martinez Appendix A regular-expression phase rows, and to Cook 2004’s `C2 18/10/14` tape encoding. It does not correspond to Cook’s multi-frame geometric tracking of `Ē`, `A4`, acceptors, rejectors, or invisibles.

### 4.3 Upgrade path for detect failures

To close the 11 detect failures, detector ownership should move from single-row `C2(A,*)` scanning to a two-stage paper-anchored detector:

1. Stage A: build an ether-relative phase scanner over all Martinez `Ph1` rows, not only `C2(A,*)`. Anchor: Martinez 2007 Appendix A, pages 29-40, plus phase semantics in §4.4 lines 771-819.
2. Stage B: track candidate gliders over multiple rows using Cook/Martinez period and displacement table. A candidate `g` must reappear after its period with the Table 2 displacement: e.g. `C2` period 7 displacement 0, `Ē` period 30 displacement -8, `F` period 36 displacement -4. Anchor: Martinez 2007 Table 2 lines 184-205.
3. Stage C: decode data from preserved spacing between tracked glider centers, not from first-row string offsets alone. Anchor: Cook 2004 spacing rules `C2 18/10/14` lines 1252-1257 and Cook 2004 crossing-preserves-spacing lines 829-848.

This is a scope change from row-pattern detection to phase-plus-motion detection. It is justified by the papers because collisions and data are defined by relative spacings and period/displacement behavior, not only by one row substring.

## Part 5: Polynomial time bound

### 5.1 TM to tag-system bound

Neary-Woods 2007 states that Rule 110 simulates Turing machines efficiently in polynomial time `O(t^3 log t)` and notes a further `O(t^2 log t)` result as unpublished in that paper (Neary-Woods 2007, PDF page 4, §2, lines 180-184). The same paragraph states Rule 110 simulates cyclic tag systems in linear time and the weak machines simulate Rule 110 with quadratic time increase, yielding `O(t^4 log^2 t)` for those machines (Neary-Woods 2007, PDF page 4, §2, lines 183-187). This PDF does not provide a separate tape length formula `g(L)` for Cook’s compiler; it gives time-overhead bounds and the repeated-word Rule 110 instance shape (Neary-Woods 2007, PDF page 4, lines 205-215).

Cook 2009’s own compiler size statement is polynomial in the size of the TM initial configuration (Cook 2009, PDF page 3, §1.2, lines 152-159). It does not spell out a closed-form `f(T)` or `g(L)` in the extracted text.

### 5.2 Tag to cyclic tag to Rule 110

Cook 2009 converts tag alphabet symbol `φ_i` into unary `N^{i-1} Y N^{|Φ|-i}` and extends the cyclic list to `s|Φ|` appendants (Cook 2009, PDF page 3, §1.3, lines 170-184). If cyclic appendants are not multiples of six, each symbol is expanded by adding five `N`s and the appendant list is expanded by five empty appendants after every appendant; the expanded system performs the same computation “on every sixth step” (Cook 2009, PDF page 1, §1, lines 49-60). Therefore the CTS step ratio in this normalization is 6 expanded CTS steps per original CTS step.

Rule 110 row width comes from three regions: left periodic `[A]v B [A]13 B [A]11 B [A]12 B`, central `C + (E/F)D...G`, and repeated right appendant block string. The concrete formula available in text is for `v`: `76*Y + 80*N + 60*nonempty + 43*empty` (Cook 2009, PDF page 6, §1.4, lines 292-296). The PDF text does not expose per-block t=0 cell widths, so a complete row-width formula requires visual extraction of Figures 1-2. Cook 2009 Figures 6-11 and Cook 2004 Figure 12 add collision, leader, ossifier, and data-spacing anchors, but they do not expose the Figure 1-2 block row widths needed for a complete initial-row width formula.

### 5.3 Scale frontier gap

The project scale frontier is encoded in `rule110/tests/test_cook_packet_scale.c`: the passing frontier variable records largest passing case; cases include `scale_3p_3t_2048`, then `scale_4p_4t_4096`, `scale_5p_5t_8192`, `scale_3p_8t_8192`, and `scale_2p_16t_16384` (lines 141-220). The encoder uses fixed guard/stride constants: leading guard 64 ether periods, leader-to-ossifier 32, min ossifier stride 64, ossifier-to-data 96, symbol stride 64 (rule110/encoder/cook_encode.c lines 43-48, 265-288). This is not Cook 2009’s global block compiler with `v` based on all appendants and right-period repetition.

The theoretical bound says polynomial size/time, not that small finite layouts pass with a fixed `4096` or `8192` step bound. The observed 3p x 3t x 2048 frontier is therefore not comparable as a constant-factor miss until the implementation uses Cook’s full left/right periodic block recipes. Because project layout uses fixed local strides while Cook’s `v` scales with total appendant content and empty/nonempty counts, the gap is an algorithm/scope gap, not merely a numeric constant error (Cook 2009, PDF page 6, lines 292-300; project file `cook_encode.c` lines 43-53 and 265-410).

## Part 6: Project findings

| finding | type | paper source | project source | status |
|---|---|---|---|---|
| `B̂` phase catalog absent: all 12 Appendix entries missing | missing data | Martinez 2007 Appendix A.5, PDF page 30, lines 1361-1375 | `rule110/encoder/glider_phases.c` lines 15-208 | **closed by W16** |
| ordinary `E` phase catalog absent: 16 Appendix entries missing; project has `Ebar` but not `E` | missing data | Martinez 2007 Appendix A.11, PDF page 32, lines 1450-1469 | `rule110/encoder/glider_phases.c` lines 85-116 only cover `Ebar` | **closed by W16** |
| `H` catalog only covers neighbor `A`; 96 parsed `H` extension rows absent | missing data | Martinez 2007 Appendix A.15, PDF pages 35-38, lines 1630-1763 | `rule110/encoder/glider_phases.c` lines 201-204 | **closed by W16** |
| glider gun catalog only covers neighbor `A`; 77 parsed extension rows absent | missing data | Martinez 2007 Appendix A.16, PDF pages 38-40, lines 1765-1873 | `rule110/encoder/glider_phases.c` lines 205-208 | **closed by W16** |
| Table 2 `F(H,f1_1)-e-B̄(C,f1_1)` outcome is `{Ē, A⁵}`, not `{Ē, A³}` | transcription error if any downstream table says `A^3` | Martinez 2012 Table 2, PDF page 11 / printed page 127, lines 498-500 | `rule110/encoder/cook_collisions.c` line 55 is correct | **closed by typo-fix commit `abdcbfa53`** |
| Table 2 OCR drops overlines in the `B̄` column; any automated extraction must preserve table-column semantics | transcription risk | Martinez 2012 Table 2, PDF page 11, lines 485-507 | `rule110/encoder/cook_collisions.c` lines 47-61 | **open: mitigated by report extraction and citation rule** |
| Decoder scans only `C2(A,phase)` and fixed packet spacings; it does not track period/displacement across frames | wrong algorithm for collision-rich detection | Martinez 2007 Table 2 lines 184-205; Cook 2004 crossing/spacing lines 829-848 | `rule110/encoder/cook_decode.c` lines 194-258 | **closed by W18 + W19** |
| Encoder layout uses fixed guards/strides instead of Cook 2009 block compiler with right periodic appendant string and left `v` formula | scope choice | Cook 2009 §1.4, PDF pages 4-6, lines 202-300 | `rule110/encoder/cook_encode.c` lines 43-53 and 236-410 | **closed by W15** |
| Data block phase emitter only emits first tape bit in `cook_data_block_emit_phase_exact` | scope choice | Cook 2004 tape encoding uses four `C2`s per character, lines 1252-1257 | `rule110/encoder/cook_data_block.c` lines 108-146 | **closed by W17** |
| Leader emitter uses eight `Ebar` plus four `C2` with uniform local spacings; Cook’s leader semantics are diagrammatic and accept/reject dependent | wrong algorithm for full Cook leader | Cook 2004 Figure 12, lines 1090-1129; Cook 2009 Figures 8-11, lines 759-933 | `rule110/encoder/cook_leader.c` lines 9-14 and 116-193 | **closed by W17** |
| Ossifier emitter uses two A4 groups, while Cook 2004 states an ossifier consists of four `A4`s converting four `Ē`s into four `C2`s | wrong algorithm for full ossifier | Cook 2004 lines 1147-1155; gap form lines 1224-1227 | `rule110/encoder/cook_ossifier.c` lines 7-13 and 105-127 | **closed by W17** |
| Cook Figure 12 `N` tape data uses `18,10,14`, and acceptor/rejector products are `A4 A1 A` / `A3` | DISCREPANCY | Cook 2004 Figure 12 and lines 1090-1112, 1252-1257 | `cook_data_block.c`; `cook_decode.c`; `cook_leader.c` | **closed by W26** |
| Cook 2009 figure-level `k`, pass-through, prepared-leader, and ossifier branch formulas are not fully represented in phase-exact emitters | DISCREPANCY | Cook 2009 Figures 6, 8, 10, 11, lines 639-933 | `cook_data_block.c`; `cook_leader.c`; `cook_ossifier.c` | **closed for Figures 6 and 8 by W30; Figure 11 by W33; Figure 10 by W35** |

## Part 7: Exhaustiveness audit

`tools/manifest_exhaustiveness_audit.c` audits the finite-witness reading of
selected FKernel, GroundCompiler, and Beyond-FKernel manifests by enumerating a
finite closure slice and comparing it with the assertion inputs listed in the
corresponding `.enum.ct` file.

`BMark` is nullary, so depth `1` is the whole closed domain. Recursive `BHist`
and BHist-derived relations use small bounded slices; these are explicit
finite-witness audits of the manifest slice, not claims about the infinite
recursive closure.

Current result:

```text
31 audit targets
17 strict PASS
14 convention bound
0 partial coverage
0 parse/enumeration failure
```

Strict PASS targets are:

```text
BMark / msame_refl: 2/2
BMark / msame_symm: 4/4
BMark / msame_trans: 8/8
BMark / msame_no_confusion: 2/2
BHist / hsame_refl: 3/3
BHist / hsame_symm: 9/9
BHist / hsame_empty_inversion: 5/5
BHist / hsame_constructor_distinct: 6/6
Ext / ext_step: 6/6
Cont / cont_basic: 9/9
Unary / unary_basic: 7/7
ExternalBinary / external_binary_basic: 9/9
GroundCompiler / flow_round_trip: 3/3
GroundCompiler / reject_reasons: 6/6
CircleModN / modn_classifier_concrete_rows: 3/3
CircleModN / modn_singleton_operation_descent: 3/3
MetaCICBHist / bhistLen_natToBHist: 4/4
```

Strict recursive slices are exact where the closure side is small: `BHist /
hsame_symm` contains six non-initial ordered depth-`1` pairs from the Lean
`BHist.Empty/e0/e1` constructors and `hsame := Eq`; `Ext / ext_step` contains
two non-initial positive constructor witnesses from `Ext.e0` and `Ext.e1`;
`Cont / cont_basic` and `ExternalBinary / external_binary_basic` contain five
non-initial append witnesses each from `Cont h k r := r = append h k` and
`BWord := BHist`; `Unary / unary_basic` contains the depth-`2` non-unary
`e0(e0 Empty)` row. The strict Beyond-FKernel slices are exact for ModN
singleton-carrier rows through unary modulus depth `2` and for MetaCIC all-e0
`natToBHist` rows through depth `3`.

Convention-bound targets remain visible in strict output. `BHist /
hsame_trans` is `6/27` because ordered triples over recursive `BHist` grow
cubically and the manifest records representative equality/vacuity triples.
`SigRel / sigrel_basic` and `SameSig / samesig_equiv` are `0/27` against their
depth-`1` fixture closures because Lean `SigRel` recurses over `ProbeBundle`
and abstract `AskSetup`, while their manifests record semantic examples.
`Ask / ask_basic` is `8/24` because Lean `AskSetup` has abstract `ProbeName`,
`Evidence`, and `Ask` fields and the C manifest fixes one executable policy.
`GroundCompiler / bhist_injectivity` is `4/9` because the Lean channel
theorems range over recursive BHist event streams while the manifest keeps six
representative stream-pair rows.

Beyond-FKernel convention-bound targets cover the four derived manifest
modules. `CircleS1 / s1_e1_components_carrier_exactness` is `2/9` over the
depth-`1` dx/dy tail surface. The three `FoldMomentKernelUp` targets are each
`1/3` over a depth-`1` window-varying nine-field carrier slice. `MetaCICAtom /
inferAtom` is `6/20` over sort and var atoms in sort-only contexts through
length `3`, and `MetaCICBHist / bhistToTerm_injective` is `6/12` over the
mixed closedness/injectivity surface. The two finite-base topology carrier
targets are each `1/18`, and `TopologyLedgerRow / ledger_constructor_tags` is
`9/21` over the six constructor tags plus pairwise no-confusion rows.

The strict gate is `make test-exhaustiveness`. Default `make test` runs the
same tool in reporting mode.

## Part 8: End-to-end TM simulation

`encoder/tm_to_tag.c` implements the Cook 2009 §1.2 Cocke-Minsky
transformation for a finite `TMSpec`. For an input machine with `m` states and
`t` symbols it uses deletion number `s=t+2`, creates the alphabet
`H/L/R/R*` per state plus `H/L/R` state-symbol rows, and fills the displayed
rule families from Cook 2009 PDF page 2-3, §1.2. The pilot test uses a
three-state binary machine over initial tape `000`; the direct C TM runner
halts with tape `110`.

`encoder/tag_to_cyclic.c` implements Cook 2009 §1.3: tag symbol `phi_i` is
encoded as `N^{i-1} Y N^{|Phi|-i}`, the ordered tag-rule appendants become the
first `|Phi|` cyclic appendants, and empty appendants extend the cyclic list to
`s|Phi|`. The compiled three-state pilot has `|Phi|=48`, `s=4`, and therefore
`192` cyclic appendants.

`tests/test_tm_end_to_end.c` checks both compiler boundaries and the physical
Rule 110 path. The full pilot TM is compiled through TM to tag to cyclic tag,
and the resulting dimensions are checked against the Cook formulas. A compact
two-symbol tag-system case then runs
`tag_to_cyclic -> cook_encode_phase_exact -> r110_run_n_steps ->
cook_decode_output`; its decoded cyclic tape is compared against
`evaluator/cyclic_tag.c` on the same generated cyclic system, and the decoded
unary tape reads back to the expected tag symbol.

`tests/test_tm_minimal_full.c` measures the smallest `TMSpec` instances that
can pass through the same compiler. With the Cook §1.2 alphabet formula
`4m+3m(t+2)` and deletion number `t+2`, even the one-state halted binary
machine compiles to `|Phi|=16`, `s=4`, hence `64` cyclic appendants and an
initial cyclic tape of length `64`. The single active transition machine
`(q0,0) -> write 1, halt` compiles to `|Phi|=32`, `s=4`, hence `128`
cyclic appendants and an initial cyclic tape of length `128`. The test runs
the C TM interpreter to the expected tape, compiles through TM to tag to cyclic
tag, runs the cyclic-tag reference evaluator for the phase-exact ledger round,
and decodes the unary cyclic string back to tag symbols. It also decodes the
initial tag tape back to the TM tape byte-for-byte.

The complete TM-generated cyclic systems are outside the current physical
Rule 110 packet frontier. The tested frontier contains small finite packet
cases such as `8p x 8t x 16384` and `2p x 32t x 32768`; the smallest
TM-generated case is already `64p x 64t`. The physical Rule 110 capstone for a
TM-generated system is therefore blocked by scale, while the compiler and
inverse boundaries are exercised without replacing the TM-generated system by
a compact fixture.
