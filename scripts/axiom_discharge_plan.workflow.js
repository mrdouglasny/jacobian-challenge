// Workflow script: produce per-axiom discharge plans + a dependency-ordered
// roadmap for jacobian-challenge (99 axioms across 28 files).
//
// HOW TO RUN (from a Claude Code session in this repo, with multi-agent
// orchestration opted in):
//   Workflow({ scriptPath: "scripts/axiom_discharge_plan.workflow.js" })
// It runs ~28 read-only Explore agents (one per file) + 1 synthesis agent,
// then RETURNS { roadmap, ... }. Write `roadmap` to
// docs/axiom-discharge-roadmap.md after it returns (the workflow sandbox
// cannot write files itself).
//
// File list below was produced by lean-fleet/scan_fleet.py scoped to the
// `Jacobians` lean_lib (matches count_axioms.sh scope). Regenerate if the
// axiom set changes. NOTE: scan has a minor false-positive (a wrapped
// signature word); agents mark such entries route="spurious".

export const meta = {
  name: 'jc-axiom-discharge-plans',
  description: 'Per-axiom discharge plans + dependency-ordered roadmap for jacobian-challenge (99 axioms, 28 files)',
  phases: [
    { title: 'Plan', detail: 'one Explore agent per file -> structured per-axiom discharge plans' },
    { title: 'Synthesize', detail: 'aggregate plans into a dependency-ordered roadmap' },
  ],
}

const REPO = '/Users/mdouglas/Documents/GitHub/jacobian-challenge'
const CATALOGS = '/Users/mdouglas/Documents/GitHub/catalogs/ALL_LEMMAS.tsv'

const FILES = [
  "Jacobians/Axioms/AbelJacobiMap.lean",
  "Jacobians/Axioms/AbelTheorem.lean",
  "Jacobians/Axioms/AnalyticCycleBasis.lean",
  "Jacobians/Axioms/BranchLocus.lean",
  "Jacobians/Axioms/HyperellipticLiouville.lean",
  "Jacobians/Axioms/IntersectionForm.lean",
  "Jacobians/Axioms/PeriodLattice.lean",
  "Jacobians/Axioms/PluckerFormula.lean",
  "Jacobians/Axioms/RiemannBilinear.lean",
  "Jacobians/Axioms/RiemannRoch.lean",
  "Jacobians/Axioms/SerreDuality.lean",
  "Jacobians/Axioms/Uniformization0.lean",
  "Jacobians/Axioms/UniversalProperty.lean",
  "Jacobians/Bridge/KirovLineIntegral.lean",
  "Jacobians/GeneralResults/InverseFunctionTheorem.lean",
  "Jacobians/ProjectiveCurve/Elliptic/Witnesses.lean",
  "Jacobians/ProjectiveCurve/Hyperelliptic.lean",
  "Jacobians/ProjectiveCurve/Hyperelliptic/AffineForm.lean",
  "Jacobians/ProjectiveCurve/Hyperelliptic/Basic.lean",
  "Jacobians/ProjectiveCurve/Hyperelliptic/Even.lean",
  "Jacobians/ProjectiveCurve/Hyperelliptic/EvenAtlas.lean",
  "Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean",
  "Jacobians/ProjectiveCurve/Line/Witnesses.lean",
  "Jacobians/ProjectiveCurve/PlaneCurve.lean",
  "Jacobians/RiemannSurface/LineBundle.lean",
  "Jacobians/RiemannSurface/PathIntegral.lean",
  "Jacobians/Vendor/Kirov/Genus.lean",
  "Jacobians/Vendor/Kirov/HolomorphicForms.lean",
]

const PLAN_SCHEMA = {
  type: 'object',
  properties: {
    file: { type: 'string' },
    plans: {
      type: 'array',
      items: {
        type: 'object',
        properties: {
          name: { type: 'string', description: 'axiom name' },
          statement: { type: 'string', description: 'one-line plain-English statement' },
          why_axiomatized: { type: 'string', description: 'why it is currently an axiom (from docstring)' },
          route: { type: 'string', enum: ['mathlib-now', 'provable-from-other-axioms', 'needs-infra', 'genuine-textbook', 'spurious'] },
          findings: { type: 'string', description: 'catalog/Mathlib search hits: exact decl names found, or "none found"' },
          prereqs: { type: 'array', items: { type: 'string' } },
          blocked_by: { type: 'array', items: { type: 'string' }, description: 'OTHER axiom names this discharge depends on' },
          effort: { type: 'integer', description: '1 (trivial) .. 10 (multi-month project)' },
          references: { type: 'string' },
        },
        required: ['name', 'statement', 'route', 'findings', 'effort', 'blocked_by'],
      },
    },
  },
  required: ['file', 'plans'],
}

phase('Plan')
const results = await parallel(FILES.map((f) => () =>
  agent(
    `You are producing AXIOM DISCHARGE PLANS for one file of the Lean 4 project at ${REPO}.

FILE: ${f}

Steps:
1. Read ${REPO}/${f}. Enumerate every \`axiom\` (and \`private axiom\`) declaration in it. Ignore false positives (e.g. a word captured from a wrapped signature that is not actually an axiom name) — mark any such entry route="spurious".
2. For each real axiom, read its docstring (statement, "why axiomatized", references, history) and find its row in ${REPO}/AXIOM_AUDIT.md if present.
3. SEARCH whether it is now dischargeable: grep ${CATALOGS} for the concept/decl name (our cross-project proved-lemma index); and use Lean Mathlib search tools if available (ToolSearch for lean_leansearch / lean_loogle / lean_local_search) plus your own Mathlib knowledge. Report EXACT decl names found, or "none found".
4. Classify each axiom's route:
   - mathlib-now: a Mathlib (or catalogs) decl now proves it directly -> cheap discharge.
   - provable-from-other-axioms: derivable from other (already-stated) decls/axioms in THIS project.
   - needs-infra: provable but requires building a bounded piece of missing infrastructure first.
   - genuine-textbook: a deep classical theorem (sheaf cohomology, Riemann-Roch, Serre duality, ...) that is a real multi-month gap.
   - spurious: not actually an axiom.
5. Fill blocked_by with OTHER axiom names (anywhere in this project) whose discharge must come first. Give an effort 1..10.

Be concrete and honest — this roadmap decides where real work goes. Return the structured object for THIS file only.`,
    { label: `plan:${f.split('/').pop()}`, phase: 'Plan', schema: PLAN_SCHEMA, agentType: 'Explore' }
  )
))

const filePlans = results.filter(Boolean)
const allPlans = filePlans.flatMap((r) => (r.plans || []).map((p) => ({ ...p, file: r.file })))
const real = allPlans.filter((p) => p.route !== 'spurious')
log(`collected ${allPlans.length} entries (${real.length} real axioms) from ${filePlans.length}/${FILES.length} files`)

phase('Synthesize')
const roadmap = await agent(
  `You are writing a dependency-ordered AXIOM DISCHARGE ROADMAP for the Lean project jacobian-challenge, as a single Markdown document.

Here are the per-axiom discharge plans (JSON, ${real.length} real axioms across ${filePlans.length} files):

${JSON.stringify(real)}

Produce a Markdown document with:
1. A title and a 2-3 sentence orientation.
2. A SUMMARY table: count of axioms by route (mathlib-now / provable-from-other-axioms / needs-infra / genuine-textbook), and the total.
3. "## Discharge now (cheap wins)": every mathlib-now and provable-from-other-axioms axiom, as a checklist with its name, file, the exact Mathlib/catalog decl to use (from findings), and effort. Order by ascending effort.
4. "## Bounded infrastructure (needs-infra)": grouped by the infrastructure piece they share; for each, what to build, which axioms it unblocks, effort.
5. "## Genuine deep gaps (textbook)": the real multi-month theorems, each with its statement, why it is a gap, and what it blocks downstream (use blocked_by edges across all axioms to show the dependency order — what must be discharged before what). Present as a topological ordering / dependency outline so it is clear what unblocks the most.
6. "## Full per-axiom table": name | file | route | effort | findings | blocked_by — every real axiom.

Use the blocked_by edges to compute the dependency ordering in sections 5/6. Be precise; cite the exact decl names from findings. Return ONLY the Markdown document text.`,
  { label: 'synthesize:roadmap', phase: 'Synthesize', agentType: 'Explore' }
)

return { roadmap, real_count: real.length, files_done: filePlans.length, plans: allPlans }
