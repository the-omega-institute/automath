import Mathlib.Tactic

namespace Omega.POM

/-- Tokens used by the MOM-prefix rewrite system. The neutral token carries multiplicative
weight `1`, so inserting or deleting it preserves the associated MOM product. -/
inductive pom_mom_prefix_product_invariant_token where
  | neutral
  | mom
  | prefix
  deriving DecidableEq, Repr

/-- Multiplicative weight attached to each token. -/
def pom_mom_prefix_product_invariant_token_weight :
    pom_mom_prefix_product_invariant_token → ℕ
  | .neutral => 1
  | .mom => 2
  | .prefix => 3

/-- Product of the token weights along a word. -/
def pom_mom_prefix_product_invariant_mom_product :
    List pom_mom_prefix_product_invariant_token → ℕ
  | [] => 1
  | t :: w =>
      pom_mom_prefix_product_invariant_token_weight t *
        pom_mom_prefix_product_invariant_mom_product w

/-- Primitive rewrites. Each rule only inserts or deletes a neutral token, hence preserves the
MOM product. -/
inductive pom_mom_prefix_product_invariant_rewrite :
    List pom_mom_prefix_product_invariant_token →
      List pom_mom_prefix_product_invariant_token → Prop where
  | drop_neutral (u v : List pom_mom_prefix_product_invariant_token) :
      pom_mom_prefix_product_invariant_rewrite
        (u ++ pom_mom_prefix_product_invariant_token.neutral :: v) (u ++ v)
  | expand_mom (u v : List pom_mom_prefix_product_invariant_token) :
      pom_mom_prefix_product_invariant_rewrite
        (u ++ pom_mom_prefix_product_invariant_token.mom :: v)
        (u ++ pom_mom_prefix_product_invariant_token.neutral ::
          pom_mom_prefix_product_invariant_token.mom :: v)
  | expand_prefix (u v : List pom_mom_prefix_product_invariant_token) :
      pom_mom_prefix_product_invariant_rewrite
        (u ++ pom_mom_prefix_product_invariant_token.prefix :: v)
        (u ++ pom_mom_prefix_product_invariant_token.prefix ::
          pom_mom_prefix_product_invariant_token.neutral :: v)

/-- Reflexive-transitive closure of the primitive rewrites. -/
inductive pom_mom_prefix_product_invariant_rewrite_closure :
    List pom_mom_prefix_product_invariant_token →
      List pom_mom_prefix_product_invariant_token → Prop where
  | refl (w : List pom_mom_prefix_product_invariant_token) :
      pom_mom_prefix_product_invariant_rewrite_closure w w
  | tail {u v w : List pom_mom_prefix_product_invariant_token} :
      pom_mom_prefix_product_invariant_rewrite u v →
        pom_mom_prefix_product_invariant_rewrite_closure v w →
          pom_mom_prefix_product_invariant_rewrite_closure u w

lemma pom_mom_prefix_product_invariant_mom_product_append
    (u v : List pom_mom_prefix_product_invariant_token) :
    pom_mom_prefix_product_invariant_mom_product (u ++ v) =
      pom_mom_prefix_product_invariant_mom_product u *
        pom_mom_prefix_product_invariant_mom_product v := by
  induction u with
  | nil =>
      simp [pom_mom_prefix_product_invariant_mom_product]
  | cons t u ih =>
      simp [pom_mom_prefix_product_invariant_mom_product, ih, Nat.mul_assoc, Nat.mul_comm]

lemma pom_mom_prefix_product_invariant_rewrite_preserves_mom_product
    {w w' : List pom_mom_prefix_product_invariant_token}
    (h : pom_mom_prefix_product_invariant_rewrite w w') :
    pom_mom_prefix_product_invariant_mom_product w =
      pom_mom_prefix_product_invariant_mom_product w' := by
  cases h <;>
    simp [pom_mom_prefix_product_invariant_mom_product_append,
      pom_mom_prefix_product_invariant_mom_product,
      pom_mom_prefix_product_invariant_token_weight, Nat.mul_left_comm]

/-- Paper label: `prop:pom-mom-prefix-product-invariant`. -/
theorem paper_pom_mom_prefix_product_invariant
    {w w' : List pom_mom_prefix_product_invariant_token} :
    pom_mom_prefix_product_invariant_rewrite_closure w w' →
      pom_mom_prefix_product_invariant_mom_product w =
        pom_mom_prefix_product_invariant_mom_product w' := by
  intro h
  induction h with
  | refl _ =>
      rfl
  | @tail u v w hstep _ ih =>
      calc
        pom_mom_prefix_product_invariant_mom_product u =
            pom_mom_prefix_product_invariant_mom_product v :=
          pom_mom_prefix_product_invariant_rewrite_preserves_mom_product hstep
        _ = pom_mom_prefix_product_invariant_mom_product w := ih

end Omega.POM
