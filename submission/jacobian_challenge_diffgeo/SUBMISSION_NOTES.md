# lean-eval submission metadata — jacobian_challenge_diffgeo

The form fields entered for the Lean FRO lean-eval submission
(lean-eval-submissions #312), preserved verbatim for reuse on resubmission.

## Model

Claude Fable 5 (primary) + Opus 4.8 / Sonnet 4.6; Codex/GPT-5.4 rescue; Gemini axiom vetting

## How this solution was produced (optional)

Multi-agent community project (mrdouglasny/jacobian-challenge) under light human steering; zero human-written Lean. Claude Code with Claude Fable 5 (also Opus 4.8 / Sonnet 4.6), Codex/GPT-5.4 rescue passes, and Gemini deep-think axiom vetting; ~8 weeks wall-clock. An independent, complementary solution to Rado Kirov's (the first lean-eval pass): a different construction (period-lattice / H1 route), with explicit positive-genus curve instances (elliptic, hyperelliptic, plane) and a machine-checked finding that Buzzard's 24 requirements are non-categorical, plus the Albanese universal-property repair. All 24 obligations sorry-free and axiom-free [propext, Classical.choice, Quot.sound], confirmed by a local Lean FRO comparator run on main. Builds on Rado Kirov's Dolbeault library (rkirov/jacobian-claude, Apache 2.0, vendored) and Michal Wallace's modules (tangentstorm/JacobianChallenge, MIT).
