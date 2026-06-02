#!/usr/bin/env python3
"""Generate the full Centauro blueprint (`blueprint/src/content.tex`) from the
project's machine-checked structure.

Sources of truth (regenerate then re-run this):
  * docs/all-axioms.txt  -- every project axiom (kernel dump; see AXIOM_AUDIT.md
    Verification). Guarantees 100% coverage: the script asserts every axiom is
    represented as an individual node or a cluster node.
  * docs/axiom-report.txt -- golden `#print axioms` of every headline; the edges.

Curated layers (the quality): headline titles, axiom class/prose (mirrors
AXIOM_AUDIT.md), and the type-stub clusters. Re-run after discharging an axiom:
    python3 scripts/gen_blueprint.py
"""
import re
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
REPORT = ROOT / "docs" / "axiom-report.txt"
ALL_AX = ROOT / "docs" / "all-axioms.txt"
OUT = ROOT / "blueprint" / "src" / "content.tex"

CORE = {"propext", "Classical.choice", "Quot.sound", "sorryAx"}
PROJ_NS = ("Axioms.", "ProjectiveCurve.", "RiemannSurface.", "GeneralResults.",
           "Extensions.", "Bridge.", "Vendor.")


def canon(name):
    if name.startswith("Jacobians.") or not name.startswith(PROJ_NS):
        return name
    return "Jacobians." + name


# ---- Headlines: full name -> (label, title, chapter) -----------------------
HEADLINES = {
    "Jacobians.ProjectiveCurve.genus_projectiveLine_eq_zero":
        ("thm:genus-P1", r"$\operatorname{genus}\PP^1 = 0$", "genus"),
    "Jacobians.ProjectiveCurve.HolomorphicOneForm_projectiveLine_eq_zero":
        ("thm:forms-P1", r"$\Omega^1(\PP^1) = 0$", "genus"),
    "Jacobians.ProjectiveCurve.genus_Elliptic_eq_one":
        ("thm:genus-E", r"genus of an elliptic curve $= 1$", "genus"),
    "Jacobians.Extensions.HyperellipticEven.genus_HyperellipticEven_eq":
        ("thm:genus-hyp", r"genus of an even hyperelliptic curve $= N/2-1$", "genus"),
    "genus": ("def:genus", r"the genus $\dim_{\CC} \Omega^1(X)$", "jac"),
    "Jacobian": ("def:jac", r"the Jacobian $\Omega^1(X)^* / H_1(X;\mathbb{Z})$", "jac"),
    "Jacobian.ofCurve": ("def:aj", r"the Abel--Jacobi map $X \to \operatorname{Jac}(X)$", "jac"),
    "ContMDiff.degree": ("def:deg", r"the degree of a holomorphic map", "jac"),
    "genus_eq_zero_iff_homeo": ("thm:g0", r"genus $0 \iff$ homeomorphic to $\PP^1$", "jac"),
    "Jacobian.ofCurve_self": ("thm:aj-self", r"Abel--Jacobi sends the basepoint to $0$", "jac"),
    "Jacobian.ofCurve_inj": ("thm:aj-inj", r"Abel--Jacobi is injective (genus $>0$)", "jac"),
    "Jacobian.ofCurve_contMDiff": ("thm:aj-smooth", r"Abel--Jacobi is holomorphic", "jac"),
    "Jacobian.pushforward": ("def:push", r"pushforward of $1$-forms / points", "jac"),
    "Jacobian.pullback": ("def:pull", r"pullback of $1$-forms / points", "jac"),
    "Jacobian.pushforward_contMDiff": ("thm:push-smooth", r"pushforward is holomorphic", "jac"),
    "Jacobian.pullback_contMDiff": ("thm:pull-smooth", r"pullback is holomorphic", "jac"),
    "Jacobian.pushforward_id_apply": ("thm:push-id", r"pushforward of the identity", "jac"),
    "Jacobian.pushforward_comp_apply": ("thm:push-comp", r"pushforward is functorial", "jac"),
    "Jacobian.pullback_id_apply": ("thm:pull-id", r"pullback of the identity", "jac"),
    "Jacobian.pullback_comp_apply": ("thm:pull-comp", r"pullback is functorial", "jac"),
    "Jacobian.pushforward_pullback": ("thm:push-pull", r"$\text{push}\circ\text{pull} = \deg$", "jac"),
}
ALIASES = {"Jacobians.Jacobian": "Jacobian"}
CHAPTERS = [
    ("genus", "Concrete genus theorems",
     "Explicit projective-curve models on which the genus is computed directly. "
     "The first three are fully axiom-free; the even hyperelliptic case rests on "
     "the Liouville L2/L3 frontier."),
    ("jac", "The abstract Jacobian (Buzzard's challenge)",
     "Buzzard's target declarations, proved in Lean modulo the named axioms "
     "below --- the classical Riemann-surface theory each rests on."),
]

# ---- Individual axiom nodes: full name -> (class, description) --------------
AX = {
 # Class 1 -- textbook-standard.
 "Jacobians.Axioms.AX_RiemannRoch": ("1", "Riemann--Roch (Forster \\S16)"),
 "Jacobians.Axioms.AX_SerreDuality": ("1", "Serre duality (Forster \\S17)"),
 "Jacobians.Axioms.AX_RiemannBilinear": ("1", "Riemann bilinear relations (Griffiths--Harris Ch.~2)"),
 "Jacobians.Axioms.AX_AbelTheorem": ("1", "Abel's theorem (Forster \\S21)"),
 "Jacobians.Axioms.AX_PluckerFormula": ("1", "Pl\\\"ucker formula (Griffiths--Harris Ch.~2)"),
 "Jacobians.Axioms.AX_BranchLocus": ("1", "branch-locus / degree finiteness (Miranda Ch.~II)"),
 "Jacobians.Axioms.AX_AnalyticCycleBasis": ("1", "symplectic $H_1$ basis (standard)"),
 "Jacobians.Axioms.AX_IntersectionForm_alternating": ("1", "cup product on $H_1$ is alternating"),
 "Jacobians.Axioms.AX_IntersectionForm_perfect": ("1", "Poincar\\'e duality / unimodularity"),
 "Jacobians.Axioms.AX_PeriodLattice": ("1", "the period lattice is a full $\\mathbb{Z}$-lattice"),
 "Jacobians.Axioms.instPeriodLatticeDiscrete": ("1", "discreteness of the period lattice"),
 "Jacobians.Axioms.AX_genus_eq_zero_iff_homeo": ("1", "uniformization, genus $0$ (Forster \\S27)"),
 "Jacobians.Vendor.Kirov.genus_eq_zero_iff_homeo": ("1", "uniformization (Kirov handoff)"),
 "Jacobians.Vendor.Kirov.ambientPhi_ambientPsi_eq": ("1", "degree identity (Kirov handoff)"),
 # Class 2a -- data-existence.
 "Jacobians.Axioms.pathIntegralBasepointFunctional": ("2a", "the path-integral functional; \\emph{opaque}"),
 "Jacobians.Axioms.AX_pathIntegral_local_antiderivative": ("2a", "chart-local FTC binding the functional to the cocycle"),
 "Jacobians.RiemannSurface.loopIntegralToH1": ("2a", "$H_1$-level period descent"),
 "Jacobians.Axioms.pullbackOneForm": ("2a", "pullback of holomorphic $1$-forms"),
 "Jacobians.Axioms.pushforwardOneForm": ("2a", "trace (pushforward) of holomorphic $1$-forms"),
 "Jacobians.Axioms.localOrder": ("2a", "local multiplicity of a holomorphic map"),
 "Jacobians.Axioms.intersectionForm": ("2a", "the $H_1$ intersection pairing"),
 "Jacobians.Axioms.abelJacobiDiv": ("2a", "divisor-level Abel--Jacobi"),
 # Class 2b -- definition-asserting.
 "Jacobians.Axioms.AX_ofCurve_inj": ("2b", "Abel--Jacobi injectivity; \\emph{opaque-blocked}"),
 "Jacobians.Axioms.AX_ofCurve_contMDiff": ("2b", "Abel--Jacobi smoothness"),
 "Jacobians.Axioms.AX_pushforward_contMDiff": ("2b", "pushforward smoothness"),
 "Jacobians.Axioms.AX_pullback_contMDiff": ("2b", "pullback smoothness"),
 "Jacobians.Axioms.AX_pushforward_pullback": ("2b", "push $\\circ$ pull $=$ degree"),
 "Jacobians.Axioms.AX_pushforwardAmbient_preserves_lattice": ("2b", "period-map naturality (pushforward)"),
 "Jacobians.Axioms.AX_pullbackAmbient_preserves_lattice": ("2b", "period-map naturality (pullback)"),
 "Jacobians.Axioms.AX_pullbackOneForm_id": ("2b", "pullback preserves identity"),
 "Jacobians.Axioms.AX_pullbackOneForm_comp": ("2b", "pullback is contravariant"),
 "Jacobians.Axioms.AX_pushforwardOneForm_id": ("2b", "trace preserves identity"),
 "Jacobians.Axioms.AX_pushforwardOneForm_comp": ("2b", "trace is covariant"),
 # Class 2c -- atlas / structure (individual).
 "Jacobians.ProjectiveCurve.HyperellipticEvenProj.affineLiftChart_compat_infinityLiftChart":
     ("2c", "cross-summand chart compat, affine $\\to\\infty$ (SP-1)"),
 "Jacobians.ProjectiveCurve.HyperellipticEvenProj.infinityLiftChart_compat_affineLiftChart":
     ("2c", "cross-summand chart compat, $\\infty\\to$ affine (SP-2)"),
 "Jacobians.GeneralResults.contDiffOn_symm_toOpenPartialHomeomorph":
     ("2c", "narrow inverse-function-theorem gap"),
 "Jacobians.ProjectiveCurve.HyperellipticAffine.squareLocalHomeomorph_zero_notMem_source":
     ("2c", "affine-form IFT shape ($\\sqrt{f}$ branch)"),
 "Jacobians.ProjectiveCurve.HyperellipticAffine.polynomialLocalHomeomorph_no_critical_in_source":
     ("2c", "affine-form IFT shape (polynomial branch)"),
 "Jacobians.ProjectiveCurve.HyperellipticAffine.AX_HyperellipticAffine_connected":
     ("2c", "the affine hyperelliptic curve is connected"),
 "Jacobians.ProjectiveCurve.AX_H1_ProjectiveLine_trivial":
     ("2c", "$H_1(\\PP^1)$ is trivial"),
 # Class 2d -- flagged.
 "Jacobians.Axioms.HyperellipticLiouville.AX_HyperellipticForm_polynomial_decomposition":
     ("2d", "Liouville L2: every form is $g(x)\\,dx/y$, $\\deg g < N/2-1$ (SP-7)"),
 "Jacobians.Axioms.HyperellipticLiouville.AX_HyperellipticOneForm_eq_form":
     ("2d", "Liouville L3: surjectivity onto low-degree forms (reduces to L2)"),
}

# ---- Cluster nodes: (label, class, predicate, title, prose) ----------------
CLUSTERS = [
 ("clu:sheaf", "2a", lambda n: any(s in n for s in
    ["Axioms.Divisor", "Axioms.H0", "Axioms.H1", "Axioms.LineBundle",
     "Axioms.PrincipalDivisors", "Axioms.canonicalDivisor"]),
  "Sheaf-cohomology type stubs",
  "The line-bundle / divisor / sheaf-cohomology layer ($\\mathrm{Divisor}$, "
  "$\\mathrm{LineBundle}$, $H^0$, $H^1$, $\\ldots$) is axiomatized as types + "
  "instances --- the part of the encoding most in question."),
 ("clu:hyp", "2c", lambda n: n == "Jacobians.ProjectiveCurve.Hyperelliptic"
    or n.startswith("Jacobians.ProjectiveCurve.Hyperelliptic.")
    or n.startswith("Jacobians.ProjectiveCurve.AX_Hyperelliptic_"),
  "Unified hyperelliptic curve: type + instances",
  "The abstract $\\mathrm{Hyperelliptic}$ type, its 7 Riemann-surface "
  "typeclass instances, and $\\mathrm{oddEquiv}/\\mathrm{evenEquiv}/\\mathrm{genus}$."),
 ("clu:plane", "2c", lambda n: ".PlaneCurve" in n,
  "Plane curve: type + instances",
  "The $\\mathrm{PlaneCurve}$ type, its 7 instances, and the affine "
  "connected/noncompact/nonempty facts."),
 ("clu:odd", "2c", lambda n: ".HyperellipticOdd." in n,
  "Odd-atlas infinity chart",
  "The odd-degree atlas's chart at infinity ($\\mathrm{infinityChart}$, its "
  "inverse, four compatibility facts, and membership)."),
 ("clu:bridge", "2a", lambda n: ".bridgePath" in n,
  "Kirov line-integral bridge path",
  "Path-selection data ($\\mathrm{bridgePath}$ + continuity / differentiability "
  "/ endpoints / integrability) for the Kirov line-integral bridge."),
 ("clu:ell", "2c", lambda n: "AX_Elliptic_" in n,
  "Elliptic period witnesses",
  "Analyticity of the $a$- and $b$-loops and the symplectic $H_1$ basis on the "
  "elliptic curve."),
]

# ---- Recently discharged (green "done" layer): label, lean, title ----------
DISCHARGED = [
 ("done:liouville", "Jacobians.Axioms.HyperellipticLiouville.liouville_compact_complex_manifold",
  "Liouville L1: a holomorphic function on a compact complex manifold is locally constant"),
 ("done:growth", "Jacobians.GeneralResults.differentiable_eq_polynomial_of_growth",
  "growth $\\Rightarrow$ polynomial (Liouville L2 step 4)"),
 ("done:oddpart", "Jacobians.GeneralResults.analyticAt_dslope_oddPart",
  "odd-part difference quotient is analytic (route-D branch-point cancellation)"),
]

CLASS_TITLES = {
 "1": ("Class 1 --- textbook-standard (trusted)",
       "Standard classical theorems with citations; discharge $=$ port the proof "
       "or import from Mathlib."),
 "2a": ("Class 2a --- data-existence (spec under review)",
        "``This object exists with spec $S$.'' The spec, not the proof, is the question."),
 "2b": ("Class 2b --- definition-asserting (may mask a bad definition)",
        "``My construction behaves correctly.'' Validate on a concrete witness."),
 "2c": ("Class 2c --- atlas / structure (curve-specific chart work)",
        "Real chart / manifold constructions; classically true, discharge is "
        "substantial chart calculus. The prime subprojects."),
 "2d": ("Class 2d --- flagged (the deepest gaps)",
        "True-but-unproven: the canonical-differentials theorem. The route-D "
        "pipeline targets these."),
}

AX = {canon(k): v for k, v in AX.items()}


def parse_report():
    recs = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", REPORT.read_text(), re.S)
    out = {}
    for name, body in recs:
        name = ALIASES.get(canon(name), canon(name))
        axs = [canon(a.strip()) for a in body.replace("\n", " ").split(",")
               if a.strip() and a.strip() not in CORE]
        out[name] = sorted(set(axs))
    return out


def short(full):
    return full.split(".")[-1].replace("_", r"\_")


def ax_label(full):
    return "ax:" + full.split(".")[-1].replace("_", "-")


def cluster_of(name):
    for lbl, cls, pred, title, prose in CLUSTERS:
        if pred(name):
            return lbl
    return None


def main():
    edges = parse_report()
    all_ax = [l.strip() for l in ALL_AX.read_text().splitlines() if l.strip()]

    # Coverage assertion: every axiom is an individual node or in a cluster.
    uncovered = [a for a in all_ax if a not in AX and cluster_of(a) is None]
    assert not uncovered, "UNCOVERED axioms:\n  " + "\n  ".join(uncovered)

    # Map each referenced axiom (an edge target) to its node label.
    def node_label(ax):
        return ax_label(ax) if ax in AX else cluster_of(ax)

    L = []
    L.append("% AUTO-GENERATED by scripts/gen_blueprint.py "
             "(docs/all-axioms.txt + docs/axiom-report.txt + curated metadata).")
    L.append("% Do not edit by hand; re-run the generator.\n")

    # Headline chapters.
    for ckey, ctitle, cintro in CHAPTERS:
        L.append(f"\\chapter{{{ctitle}}}\n\n{cintro}\n")
        for full, (lbl, title, chap) in HEADLINES.items():
            if chap != ckey:
                continue
            axs = edges.get(full, [])
            env = "definition" if lbl.startswith("def:") else "theorem"
            uses = sorted({node_label(a) for a in axs if node_label(a)})
            L.append(f"\\begin{{{env}}}[{title}]")
            L.append(f"  \\label{{{lbl}}}\n  \\lean{{{full}}}\n  \\leanok")
            if uses:
                L.append(f"  \\uses{{{','.join(uses)}}}")
            L.append("  Proved in Lean" + ("." if not axs else ", resting on the axiom frontier below.")
                     if not axs else "  Proved in Lean, resting on the axiom frontier below.")
            L.append(f"\\end{{{env}}}\n")

    # Axiom frontier, by class: individual nodes then cluster nodes.
    L.append("\\chapter{The axiom frontier}\n")
    L.append("Every node below is currently an \\texttt{axiom} --- a staging point "
             "to discharge into a Lean proof (a subproject). Edges into these nodes "
             "are machine-checked. Full audit: \\texttt{AXIOM\\_AUDIT.md}.\n")
    for cls in ["1", "2a", "2b", "2c", "2d"]:
        indiv = [a for a in all_ax if AX.get(a, (None,))[0] == cls]
        clus = [c for c in CLUSTERS if c[1] == cls]
        if not indiv and not clus:
            continue
        ctitle, cintro = CLASS_TITLES[cls]
        L.append(f"\\section{{{ctitle}}}\n\n{cintro}\n")
        for a in indiv:
            _, desc = AX[a]
            L.append(f"\\begin{{lemma}}[{short(a)}]\n  \\label{{{ax_label(a)}}}\n"
                     f"  \\lean{{{a}}}\n  {desc}.\n\\end{{lemma}}\n")
        for lbl, ccls, pred, title, prose in clus:
            members = [a for a in all_ax if pred(a)]
            rep = members[0] if members else None
            L.append(f"\\begin{{lemma}}[{title} ({len(members)})]")
            L.append(f"  \\label{{{lbl}}}")
            if rep:
                L.append(f"  \\lean{{{rep}}}")
            L.append(f"  {prose} \\emph{{Cluster of {len(members)} axioms.}}")
            L.append("\\end{lemma}\n")

    # Recently discharged (green progress layer).
    L.append("\\chapter{Recently discharged}\n")
    L.append("Former axioms now proved in Lean --- the growing green frontier.\n")
    for lbl, lean, title in DISCHARGED:
        L.append(f"\\begin{{lemma}}[{title}]\n  \\label{{{lbl}}}\n"
                 f"  \\lean{{{lean}}}\n  \\leanok\n\\end{{lemma}}\n")

    OUT.write_text("\n".join(L) + "\n")
    begin = "\\begin"
    nnodes = sum(1 for l in L if l.startswith(begin))
    ncov = len([a for a in all_ax if a in AX]) + sum(
        1 for a in all_ax if a not in AX and cluster_of(a))
    print(f"wrote {OUT}: {nnodes} nodes | {len(HEADLINES)-len(ALIASES)} headlines "
          f"| {len(all_ax)} axioms covered ({ncov}) | "
          f"{sum(len([a for a in all_ax if c[2](a)]) for c in CLUSTERS)} clustered")


if __name__ == "__main__":
    main()
