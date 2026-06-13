import Challenge
import Submission.CechModuleCat

/-!
# Submission root

Development modules live under `Submission/` and are imported here. The final
lean-eval deliverable re-declares all 9 holes under `namespace Submission`
(workspace rules: helpers not in mathlib must be inlined into the submission
workspace; `Challenge.lean` is fixed and must not be modified; comparator
runs via `lake test` in the eval workspace).

No `sorry`, no `axiom`, no `ω` as a binder name (Lean v4.30 reserves it).
-/

namespace Submission

end Submission
