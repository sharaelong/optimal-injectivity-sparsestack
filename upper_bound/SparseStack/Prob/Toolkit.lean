import SparseStack.Prob.Basic
import SparseStack.Prob.Hoeffding
import SparseStack.Prob.Resample
import SparseStack.Prob.McDiarmid
import SparseStack.Prob.Tails

/-!
# Finite probability toolkit (W-PROB)

Umbrella module. All statements live in namespace `SparseStack` on Heidary's finite laws
`SparseFock.FiniteLaw`:

1. `hoeffding_lemma` — `SparseStack/Prob/Hoeffding.lean`
2. `mcdiarmid_upper`, `mcdiarmid_lower` (+ `mcdiarmid_mgf`, `mcdiarmid_step`) —
   `SparseStack/Prob/McDiarmid.lean`
3. `paley_zygmund` — `SparseStack/Prob/Tails.lean`
4. `expect_prod_disjoint_blocks` (+ `expect_prod_disjoint_blocks_finset`,
   `expect_expect_piecewise`, `expect_mul_of_dependsOn`, partial averages `resampleAvg` with
   `resampleAvg_resampleAvg`, `expect_resampleAvg`, `resampleAvg_update_le`, ...) —
   `SparseStack/Prob/Resample.lean`
5. `weighted_bernoulli_lower_tail` (+ `one_sub_exp_neg_ge`, `exp_neg_half_le`) —
   `SparseStack/Prob/Tails.lean`
6. `subset_bound` — `SparseStack/Prob/Tails.lean`
7. `prob_le_of_subset`, `prob_union_le`, `prob_union_le_sum`, `prob_iUnion_le_sum`,
   `prob_eq_one_sub_prob_compl`, `one_sub_le_prob_of_prob_compl_le`, `one_sub_sum_le_prob`,
   `prob_congr`, indicator lemmas, `expect_mul_const`, `expect_sum`, `finiteLaw_ext`,
   `finiteLaw_nonempty` — `SparseStack/Prob/Basic.lean`
8. `expect_independentProduct_equiv`, `expect_independentProduct_sum_split`,
   `prob_independentProduct_sum_split`, `expect_independentProduct_equiv_sum_split`,
   `prob_independentProduct_equiv_sum_split` — `SparseStack/Prob/Basic.lean`
9. `uniformLaw`, `uniformLaw_weight`, `uniformLaw_expect`, `uniformLaw_prob`,
   `independentProduct_uniformLaw`, `uniformLaw_expect_comp_equiv`,
   `uniformLaw_expect_expect_equiv`, `uniformLaw_expect_equiv`, `uniformLaw_prob_equiv`;
   binary products `prodLaw`, `expect_prodLaw`,
   `prob_prodLaw`, `prodLaw_uniformLaw` — `SparseStack/Prob/Basic.lean`
-/
