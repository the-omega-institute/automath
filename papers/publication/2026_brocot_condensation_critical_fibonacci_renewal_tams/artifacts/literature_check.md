# Literature check

## Citation scope

The article cites twelve sources, all carried unchanged from the bibliography
of the source manuscript: ArmendarizLoulakis2011, Berstel2001, Carlitz1968,
Dushistova2007, Feller1971, Liehl1983, MoshchevitinZhigljavsky2004,
OmeyVanGulck2015, Panov1982, Stufler2020, Weinstein2016, and Zeckendorf1972.
No bibliographic item was added. The development pass makes the locations of
the renewal and stable-law inputs precise, so those locations were checked
against the named sources as recorded below.

The title and authors of the companion manuscript were checked against its
local `main.tex`; the companion is identified in prose rather than entered as
a published bibliographic item.

## Second-order lattice renewal input

Entry: OmeyVanGulck2015, DOI 10.1016/j.spl.2015.05.002.

- Crossref returned the title *Intuitive approximations in discrete renewal
  theory, Part 1: Regularly varying case* and lead author Edward Omey. These
  match the bibliography.
- Semantic Scholar returned the same title, authors E. Omey and S. Van Gulck,
  and the KU Leuven repository record as the open-access location.
- The KU Leuven OAI record
  `oai:lirias2repo.kuleuven.be:123456789/504142` returned the published PDF
  and the same title and authors. The PDF was checked directly.
- The asymptotic used in the paper is the first displayed assertion in
  Section 3.2, immediately following equation (8): for a tail regularly
  varying with index `-alpha`, `alpha > 1`, the renewal mass minus `1/mu` is
  asymptotic to the equilibrium tail divided by `mu`, equivalently to
  `n Fbar(n) / (mu^2 (alpha - 1))`. That assertion is unnumbered in the
  published article, so the manuscript cites its exact section and position
  rather than inventing a theorem number.

## Stable domain-of-attraction input

Entry: Feller1971, *An Introduction to Probability Theory and Its
Applications*, volume II, second edition, Wiley, 1971.

- Open Library work `OL35392227W`, edition `OL27252013M`, returned the title,
  author William Feller, publisher John Wiley & Sons, publication year 1971,
  and edition statement "2nd ed." These match the bibliography.
- The cited criterion is Chapter XVII, Section 5, Theorem 2, the stable
  domain-of-attraction criterion. The manuscript specializes it to positive
  random variables and also proves the needed characteristic-exponent
  convergence from the tail measures, so the normalization, tail balance,
  centering, and Levy measure are all written out in the paper's notation.

## Carried checks

The DOI, title, and lead-author checks recorded for the other carried entries
remain applicable. In particular, the Dushistova title and lead author match
DOI 10.1070/SM2007v198n05ABEH003854, and the Weinstein title and lead author
match DOI 10.1080/10586458.2015.1118416 and arXiv math/0307150.
