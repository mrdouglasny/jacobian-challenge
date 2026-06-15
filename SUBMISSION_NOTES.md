# lean-eval submission metadata — jacobian_challenge_diffgeo

The form fields for the Lean FRO lean-eval submission, for reuse on resubmission.
(Model attribution corrected vs the original #312 text: Claude Fable 5 was used
only in the final ~2 days, not as a primary model — the primary models across the
~8 weeks were Opus 4.8 / Sonnet 4.6.)

## Model

Claude Opus 4.8 / Sonnet 4.6 (primary); Claude Fable 5 (final ~2 days); Codex/GPT-5.4 rescue; Gemini axiom vetting

## How this solution was produced (optional)

Multi-agent community project (mrdouglasny/jacobian-challenge) under light human steering; zero human-written Lean. Claude Code with Claude Opus 4.8 and Sonnet 4.6 as the primary models (Claude Fable 5 only in the final ~2 days), Codex/GPT-5.4 rescue passes, and Gemini deep-think axiom vetting; ~8 weeks wall-clock. An independent, complementary solution to Rado Kirov's (the first lean-eval pass): a different construction (period-lattice / H1 route), with explicit positive-genus curve instances (elliptic, hyperelliptic, plane) and a machine-checked finding that Buzzard's 24 requirements are non-categorical, plus the Albanese universal-property repair. All 24 obligations sorry-free and axiom-free [propext, Classical.choice, Quot.sound], confirmed by a local Lean FRO comparator run on main. Builds on Rado Kirov's Dolbeault library (rkirov/jacobian-claude, Apache 2.0, vendored) and Michal Wallace's modules (tangentstorm/JacobianChallenge, MIT).
