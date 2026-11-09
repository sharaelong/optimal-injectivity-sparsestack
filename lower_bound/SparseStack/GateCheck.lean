import SparseStack.Gate.Gate
import SparseStack.Main

/-!
# G1 integration gate for `SparseStack` (lead-owned; NOT part of the default build target)

Runs the elaborated trust gate (`SparseStack/Gate/Gate.lean`, the shared IntMul gate with renamed
commands) on the cone of both headline theorems and on every constant of the `SparseStack` and
`SparseFockFormal` (vendored Heidary) modules in scope, then prints the headline axioms. The two
`example`s check that the headline theorems have literally the Spec types.
-/

#sstack_gate_check [SparseStack.mainTheorem, SparseStack.constantInjectionQuadratic]

#sstack_gate_modules SparseStack SparseFockFormal

#print axioms SparseStack.mainTheorem
#print axioms SparseStack.constantInjectionQuadratic

example : SparseStack.MainTheorem := SparseStack.mainTheorem
example : SparseStack.ConstantInjectionQuadratic := SparseStack.constantInjectionQuadratic
