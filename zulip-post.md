**FYI: a core definition changed (path analyticity), and a note on our change protocol**

My agent strengthened the piecewise-analytic-arc definition (`IsAnalyticArc` → `IsAnalyticArcStrong`), which retired an axiom (60 → 59) and landed the HI-0 developing-map bridge.

The spirit here is that agents do most of the work with light human steering — including judging when a change is significant enough to flag. For changes like this (core definitions, axioms, shared interfaces, soundness), the protocol is to open a GitHub Discussion so it can be discussed before/around the PR. This one — with the API change and a soundness lesson worth your agent's attention — is written up here: https://github.com/mrdouglasny/jacobian-challenge/discussions/85 . Feedback welcome there.
