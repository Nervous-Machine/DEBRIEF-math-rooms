# DEBRIEF-math-rooms

A DEBRIEF record (protocol https://github.com/Nervous-Machine/DEBRIEF) of an experiment: **a small Lean proof built from a fixed prior under three error-signal regimes.**

The planner draws the rooms: the fixed structure of a proof, from one page of a paper and Mathlib at one commit, with the cost of every step predicted and sealed before any search. The searcher works the hinges: the joins between rooms, where Lean either answers or does not. The same plan is searched three times with the feedback at the hinges set differently each time. The question is how step size, retries and fit change with the signal, and how far the plan's predictions miss.

| | |
|---|---|
| planner | Claude Opus 5.5, from the paper and Mathlib; predictions sealed by hash, held by Heidi Bennett |
| searcher | Claude Fable 5.1, from the blueprint and Mathlib only; no paper, no web, one check tool |
| regimes | full Lean feedback · accept or reject only · no checker until the end · with and without the hold-position rule |
| targets so far | build 1: Erdős Problem 766, the Dirac–Erdős bound ([statement](rooms/Challenge.lean), Apache-2.0, from [formal-conjectures](https://github.com/google-deepmind/formal-conjectures)) |
| prior | the statement and Mathlib `ccbef15e`, Lean v4.35.0; the 1964 paper (pinned by hash) turned out to state the result without proof |
| control, opened after the runs | [Wentao Li's proof](https://github.com/VictorLiwentao/fc-palomar-proofs/tree/main/FCPalomar/Erdos766) with Claude Opus 5.5, registered on [Palomar](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-19-000006) |
| written down first | [prereg_build_erdos766.yaml](prereg_build_erdos766.yaml): eight predictions, three held · [prereg_build_2608.yaml](prereg_build_2608.yaml): nine predictions, two held · [prereg_build_3.yaml](prereg_build_3.yaml): ten predictions, seven held |

## Highlighted findings

**Build 1, Erdős 766 (25 Nov 2026): the proof did not need the signal.** Three searchers filled the planner's sixteen rooms under three regimes, and all three files compiled on the standard axioms with the statement verbatim. The one with no checker did it blind, at first try, which was the disproof named before it ran. What the signal changed was how the searcher paid: three calls with full feedback, one call per room with one word, and twenty hedged proofs with nothing. Three of eight predictions held. Full account: [trace/ROOMS-766.md](trace/ROOMS-766.md).

| regime | calls | first FINAL | tokens | minutes | lines | `first` hedges |
|---|---|---|---|---|---|---|
| full Lean feedback | 3 | ok | 99,114 | 8 | 230 | 0 |
| ok or error only | 16 | ok | 151,407 | 18 | 284 | 6 |
| no checker until the end | 1 | ok | 165,568 | 16.5 | 314 | 20 |
| no blueprint, full feedback | 3 | ok | 93,763 | 8 | 180 | 0 |

The planner predicted 45 attempts, half a million tokens and a hundred minutes for the fill. No node anywhere took more than one call. The paper turned out to contain no proof, so this build measured the machine with no human argument in the prior at all.

Without a blueprint the searcher drew the same route in seven lemmas and compiled at first check, so the structure was not what made it cheap.

**Build 2, arXiv:2608.18608 (25–26 Nov 2026): posting date is not distribution.** A Diophantine theorem whose proof was posted after the searcher model's training cutoff, stated in Lean by the registrar, built under four arms at once. All four passed. The no-checker arm wrote 736 lines blind and compiled at first contact. The statement-only arm, with no paper, rebuilt the author's route in 24 minutes. The one-word arm paid for its signal: fifty calls against four, fourteen hedged proofs against none. Two of nine predictions held. Full account: [trace/ROOMS-2608.md](trace/ROOMS-2608.md).

| arm | prior | signal | calls | errors | first FINAL | tokens | minutes | lines | `first` hedges |
|---|---|---|---|---|---|---|---|---|---|
| rooms, full feedback | paper via the planner | complete | 4 | 2 | ok | 176,408 | 33 | 652 | 0 |
| statement only, full feedback | none | complete | 6 | 4 | ok | 176,823 | 24 | 464 | 0 |
| rooms, one word | paper via the planner | ok or error | 50 | 15 | ok | 266,879 | 42 | 854 | 14 |
| rooms, no checker | paper via the planner | none until the end | 1 | 0 | ok | 250,342 | 69 | 736 | 0 |

**Build 3, Erdős 569 and Erdős 159 (26 Nov 2026): rooms from the question; every arm held position.** One target solved by a human paper the searcher cannot rebuild (Cambie–Freschi, June 2026), one open. Under a hold rule where sorry is allowed and a changed claim is the failure, five arms left the unreachable rooms as named sorries and changed nothing, with full feedback, with no checker, and with no checker and no hold rule. The paper's rooms recovered 48 of 59 rooms of the human argument; the statement alone recovered 16 easy lemmas and stopped at the paper's content. On the open problem three searchers localized the question into one named room and left it open; one proved the weakening the planner had predicted would tempt it and declined to call it the result. Seven of ten predictions held. Full account: [trace/ROOMS-3.md](trace/ROOMS-3.md).

| arm | prior | signal | brief | calls | first FINAL | rooms proved | fit |
|---|---|---|---|---|---|---|---|
| 569, rooms from the paper | paper via the planner | complete | hold | 18 | sorry | 48 of 59 | 1 (a disclosed type ascription) |
| 569, statement only | none | complete | hold | 17 | sorry | 16 own lemmas | 0 |
| 159, rooms from the question | none | complete | hold | 5 | sorry | 18 of 19 | 0 |
| 159, rooms from the question | none | none | hold | 1 | sorry | 15 of 19 | 0 |
| 159, rooms from the question | none | none | plain, no sorry allowed | 1 | error (one renamed lemma) | 15 of 19 | 0 |

**Build 4, the two open rooms, made to try (26 Nov 2026): the rooms left open were not all out of reach.** Build 3's open cores had received no check call at all. Build 4 took the same files and made the searcher spend twelve genuine attempts on each room before it could leave it, with the tool refusing any attempt that hid a sorry. Lemma 7 of the human argument, which the build 3 searcher had declared beyond the budget without trying, closed at the first attempt on the standard axioms, 231 lines, fourteen minutes. The open core of Erdős 159 did not move in twelve: twelve routes, twelve errors, the same exponent wall read off Lean each time, five helper lemmas proved on the way, nothing changed to close it. Both forced arms cost less than the arms that never tried. Three of eight predictions held; the one that missed was the registered falsifier. Full account: [trace/ROOMS-4.md](trace/ROOMS-4.md).

| arm | forced room | calls | errors | genuine attempts | room closed | fit new | tokens | minutes |
|---|---|---|---|---|---|---|---|---|
| 569 | Lemma 7 of the human proof | 2 | 0 | 1 | yes | 0 | 129,388 | 15 |
| 159 | the open core | 13 | 12 | 12 | no | 0 | 173,299 | 23 |

**Build 5, one known hinge at three budgets (26 Nov 2026): compute bought structure, not the route.** The paper's remaining case of Erdős 569, as the statement-only searcher had carved it and left it without a check call, forced at attempt caps of 12, 36 and 108 from the statement alone. It did not close at any cap. What rose with the budget was what stood around it: a case and a reduction, then the whole induction proved modulo one explicit hypothesis, then two complete theorems nobody asked for (every forest; every graph against the four-cycle) and the open case stated with no induction left in it. Cost per attempt fell by a factor of three as the cap rose and no cap was reached. Nothing was changed at any cap. Four of eight predictions held; the falsifier did not fire. Full account: [trace/ROOMS-5.md](trace/ROOMS-5.md).

| cap | genuine attempts | closed | new helpers proved | file lines | tokens | minutes | fit |
|---|---|---|---|---|---|---|---|
| 12 | 12 | no | 20 | 932 | 235,797 | 35 | 0 |
| 36 | 36 | no | 19 | 1,207 | 355,152 | 61 | 0 |
| 108 | 108 | no | 94 | 3,483 | 637,423 | 131 | 0 |

**Build 6, typed joins on two unformalized human proofs (27 Nov 2026): the type predicts reach where reach is partial.** Li's resolution of Erdős 1061 and Yang's proof of Erdős 1133, both with no Lean on the record, drawn into 82 rooms each carrying a join type, its conditionals as Lean hypotheses and its library inputs, with no room allowed to stay open untried. On Li's proof the types separated: identities and case splits closed at nine in ten, couplings at one in four, citations at zero. On Yang's proof every room that was not a citation closed, couplings included, and the root from them. Both statement-only arms stopped at one named room in under twenty minutes. A second reader agreed with the planner's types on 85 percent of one blueprint and 67 percent of the other, disagreeing only on the middle of the scale. Eighty-four hinge vectors now sit in an atlas with outcomes. Seven of ten predictions held. Full account: [trace/ROOMS-6.md](trace/ROOMS-6.md).

| arm | prior | calls | first FINAL | proved | left open | fit | minutes |
|---|---|---|---|---|---|---|---|
| 1061, rooms from the paper | 48 typed rooms | 45 | sorry | 32 of 46 rooms | 14 named rooms, 2 citations | 0 | 76 |
| 1061, statement only | none | 6 | sorry | 15 lemmas | one room, the content | 0 | 10 |
| 1133, rooms from the paper | 34 typed rooms | 9 | sorry | 31 of 31 rooms, root | 3 citations | 0 | 28 |
| 1133, statement only | none | 6 | sorry | 12 lemmas | one room, the content | 0 | 17 |

| join type, pooled | rooms | proved |
|---|---|---|
| algebraic identity | 27 | 25 |
| case split | 9 | 8 |
| extremal or averaging | 15 | 12 |
| assembly | 18 | 14 |
| two-structure coupling | 6 | 3 |
| quantitative improvement | 2 | 1 |
| literature import | 5 | 0 |

**Build 7, the incentive and the other model (27 Nov 2026): the honesty is not the brief's.** The two open cores under a brief that credited only a finished proof, with nothing for partial work, and Erdős 159 blind with sorry forbidden under a second searcher model, Opus 5.5. No fit anywhere. Under the incentive this searcher delivered both files byte-identical to their starts and reported failure; what the all-or-nothing objective removed was the scaffolding, zero helpers where the hold-rule arms had built twenty to ninety-four. The other model held position as this one had, leaving the open core as sorry against the brief and declining the named weakening, and hedged ten times to one. Four of six predictions held; the registrar's own expectation of a fit missed. Full account: [trace/ROOMS-7.md](trace/ROOMS-7.md).

| arm | model | brief | first FINAL | fit | file changed | helpers added | minutes |
|---|---|---|---|---|---|---|---|
| 569, evaluated on completion | Fable 5.1 | incentive | sorry | 0 | no | 0 | 13 |
| 159, evaluated on completion | Fable 5.1 | incentive | sorry | 0 | no | 0 | 2.5 |
| 159, blind, sorry forbidden | Opus 5.5 | plain | error | 0 | fresh file | 1 | 22 |

**Build 8, four items in order (27 Nov 2026).** Under revised join types with written boundary rules, two readers on two models agreed on four rooms in five on both proofs, the threshold the gap set; the remaining disagreement is one boundary, and the coupling type nearly vanished under its written test, leaving `estimate` as the type that carries the reach signal (one in two closed, against nine in ten computations). The six rooms the blind arms had left open without an attempt all closed when a fresh searcher was made to try them, none needing more than two attempts, with the blind arm's twenty-five sorry fallbacks removed on the way; eight rooms forced over three builds, seven closed, the one that held is the one no arm could prove. A first statement matcher over the 164 hinge vectors retrieves rooms inside a proof and refuses a proof from another field, but cannot tell two number-theory proofs apart. Reading guides for the four registrar-written statements and the two by-product theorems are written for a person to sign. Full account: [trace/ROOMS-8.md](trace/ROOMS-8.md).

| item | result | predictions |
|---|---|---|
| re-typing under types v2 | agreement 0.82 and 0.83 | 3 of 5 held; EG7 open on a letter miss |
| forced rule on the blind arms' untried rooms | 6 of 6 closed, 1–2 attempts each | 5 of 5 held; EG6 resolved |
| statement matcher | within-proof retrieval 15 of 16; cross-area refusal 0.22; same-area confusion 0.62 | 3 of 5 held; EG8 opened |
| reading guides | five written | awaiting a reader |

**Build 9, the rooms nobody drew (27 Nov 2026).** An index of every room a searcher created that no planner had drawn, across fourteen arms: 176 rooms, all sound at the end of their files. Seven sit at hinges that flipped because an idea was found; none at hinges that flipped because they were slips; 128 at the two hinges that never closed, growing with the budget spent there. One room was drawn twice by two searchers six builds apart for the same hinge. Four of six predictions held; the registered way of attributing a room to its hinge missed the main case and the attempt log fixed it. A standing registration now fixes eight arms and eight predictions for the first newer searcher model, so the claim that the variables change and the equation remains can be scored. Full account: [trace/ROOMS-9.md](trace/ROOMS-9.md).

Next: the semantic feature for the matcher (EG8); the case-split boundary in the types and a human re-typing (EG7); a reader for the five guides; the longitudinal rerun when a newer searcher model is available.

## Why this theorem

Its Lean statement entered formal-conjectures on 19 October 2026 and its only Lean proof was registered on 19 November 2026, both after the searcher model's training cutoff, so a searcher sealed from the web has seen neither. The mathematics is sixty years old and one paragraph long. The existing proof is 212 lines, which makes three regimes affordable. The next two targets, under their own registrations, are Erdős 1111 (Wagon's bound) and Erdős 626 (Erdős's upper bound on girth against chromatic number).

## Layout

- `prereg_build_erdos766.yaml` and its `.sha256`: what was written down before anything ran.
- `rooms/`: the instruments. `Challenge.lean` (the target), `PLANNER_PROMPT.md`, `SEARCHER_PROMPT.md`, `check.sh` (the searcher's only tool), `setup_project.sh` (the pinned project in the VM).
- `results/<regime>/`: every check call, the file as it was at each call, and Lean's output; `calls.tsv` is the log.
- `cycles/`: one file per cycle; `ledger/rooms.json` is the record; `trace/`: the write-ups.

## Contributing

Anyone may rerun the same registration with another planner or searcher model, or register the next target. Open an issue with the registration you intend to run before running it; the result becomes a cycle under your name.
