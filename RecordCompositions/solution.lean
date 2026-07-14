import Mathlib

/-
# Problem Description

Throughout, `K` is a fixed field of characteristic zero (e.g. `K = ℚ` or `K = ℝ`).

We study a combinatorial identity connecting:
* down-up alternating permutations of `{1,...,2n}` and a "record composition" statistic,
* the Euler / zigzag numbers `E_k` (OEIS A000111), and
* the algebra `NSym` of noncommutative symmetric functions together with its image in
  the algebra `Sym` of symmetric functions.

## Main definitions (informal)

1. A *composition* of `n ≥ 0` is a finite sequence `α = (α_1,...,α_ℓ)` of positive
   integers summing to `n`.  (Modelled by `Composition n`.)
2. Its *partial sums* are `s_j = α_1 + ... + α_j`.  (Modelled by `Composition.sizeUpTo`.)
3. The Euler (zigzag) numbers `E_k`: `E_0 = E_1 = 1`, and in general the number of
   alternating permutations of `{1,...,k}`.  Set `b_k = k E_{2k-1} / (2k)!`, and for a
   partition `λ`, `b_λ = ∏ b_{λ_i}`.
4. `𝒜_{2n}`: down-up alternating permutations `w = a_1 a_2 ⋯ a_{2n}` of `{1,...,2n}`
   with `a_1 > a_2 < a_3 > a_4 < ⋯ < a_{2n-1} > a_{2n}`.
5. The odd subword `ŵ = a_1 a_3 a_5 ⋯ a_{2n-1}`.
6. The record composition `rc(ŵ)`: the composition of `n` whose parts are the gaps
   between consecutive left-to-right maxima positions of `ŵ` (with a final block up to
   `n`).
7. `N(α) = #{ w ∈ 𝒜_{2n} : rc(ŵ) = α }`.
8. `NSym = K⟨S_1, S_2, ...⟩` the free associative algebra with noncommutative power sums
   `Ψ_k` (`n S_n = ∑_{k=1}^n S_{n-k} Ψ_k`); the endomorphism `φ_b` with
   `φ_b(Ψ_k) = b_k Ψ_k`, `𝐀_n := φ_b(S_n)`; the map `χ : NSym → Sym` with `χ(S_n) = h_n`;
   and `A_n = ∑_{λ ⊢ n} z_λ^{-1} b_λ p_λ ∈ Sym`.

## Main statements

* **Statement 1.** For `n ≥ 1` and `α = (α_1,...,α_ℓ) ⊨ n`,
  `N(α) = ∏_j C(2 s_j - 1, 2 α_j - 1) E_{2 α_j - 1} = (2n)! ∏_j b_{α_j} / s_j`.
* **Statement 2.** In `NSym`, `(2n)! 𝐀_n = ∑_α N(α) Ψ^α`, and `χ(𝐀_n) = A_n` in `Sym`.

## Modelling choices

* Positions and values are `0`-indexed via `Fin (2*n)`; the informal `a_i` (`1`-indexed)
  is `w (i-1)`.  The odd subword `ŵ` picks out the `0`-indexed even positions `2k`.
* `NSym` is modelled as the free `K`-algebra on generators indexed by `ℕ`, where the
  generator `k ≥ 1` represents the noncommutative power sum `Ψ_k` (these freely generate
  `NSym`).  `Sym` is modelled as the polynomial ring `MvPolynomial ℕ K`, where `X k`
  represents the power sum `p_k` (which freely generate `Sym` over a `char 0` field);
  `χ` is the forgetful map `Ψ_k ↦ p_k`.
-/

open scoped Nat

/-! ## Euler (zigzag) numbers -/

/-- Entringer numbers, via the standard zigzag recurrence.  We only use the diagonal. -/
def entringer : ℕ → ℕ → ℕ
  | 0, _ => 1
  | (_ + 1), 0 => 0
  | (n + 1), (k + 1) => entringer (n + 1) k + entringer n (n - k)

/-- The Euler (zigzag) numbers `E_k`, OEIS A000111.  `E_k` counts alternating
permutations of `{1,...,k}`; here it is defined by the diagonal Entringer recurrence,
which yields `E_0 = E_1 = 1, E_2 = 1, E_3 = 2, E_4 = 5, E_5 = 16, ...`. -/
def euler (n : ℕ) : ℕ := entringer n n

/-- `b_k = k E_{2k-1} / (2k)!` as a rational number (Definition 3). -/
def bRat (k : ℕ) : ℚ := (k * euler (2 * k - 1)) / (Nat.factorial (2 * k))

/-! ## Compositions, partial sums

We use Mathlib's `Composition n`: `α.blocks` is the list of parts, `α.length` the length,
`α.blocksFun i` the `i`-th part (`0`-indexed), and `α.sizeUpTo j = α_1 + ... + α_j` the
`j`-th partial sum, with `α.sizeUpTo 0 = 0` and `α.sizeUpTo α.length = n`. -/

/-! ## Down-up alternating permutations and the record composition -/

section Perm
variable {n : ℕ}

/-- `w` is a down-up alternating permutation of `{1,...,2n}` (values and positions are
`0`-indexed).  In `0`-indexed one-line notation `a_j = w j`, this says
`a_0 > a_1 < a_2 > a_3 < ⋯`: even→odd positions are descents, odd→even are ascents. -/
def IsDownUp (w : Equiv.Perm (Fin (2 * n))) : Prop :=
  ∀ j : ℕ, (h : j < 2 * n - 1) →
    if Even j then w ⟨j, by omega⟩ > w ⟨j + 1, by omega⟩
    else w ⟨j, by omega⟩ < w ⟨j + 1, by omega⟩

instance (w : Equiv.Perm (Fin (2 * n))) : Decidable (IsDownUp w) :=
  Nat.decidableBallLT _ _

/-- The set `𝒜_{2n}` of down-up alternating permutations. -/
def downUpPerms (n : ℕ) : Finset (Equiv.Perm (Fin (2 * n))) :=
  {w | IsDownUp w}.toFinset

/-- The `k`-th entry of the odd subword `ŵ` (`0`-indexed): `ŵ_k = a_{2k+1}` (`1`-indexed)
`= w (2k)`. -/
def hatVal (w : Equiv.Perm (Fin (2 * n))) (k : Fin n) : Fin (2 * n) :=
  w ⟨2 * (k : ℕ), by have := k.isLt; omega⟩

/-- Position `k` (`0`-indexed, `k < n`) is a left-to-right maximum ("record") of the odd
subword `ŵ`. -/
def IsRecord (w : Equiv.Perm (Fin (2 * n))) (k : Fin n) : Prop :=
  ∀ j : Fin n, (j : ℕ) < (k : ℕ) → hatVal w j < hatVal w k

instance (w : Equiv.Perm (Fin (2 * n))) (k : Fin n) : Decidable (IsRecord w k) := by
  unfold IsRecord; infer_instance

/-- The boundary set of the record composition, as a subset of `Fin (n+1)`: the
`0`-indexed record positions together with `n`. -/
def recBoundaries (w : Equiv.Perm (Fin (2 * n))) : Finset (Fin (n + 1)) :=
  {i : Fin (n + 1) | (i : ℕ) = n ∨ ∃ h : (i : ℕ) < n, IsRecord w ⟨i, h⟩}.toFinset

lemma recBoundaries_zero_mem (w : Equiv.Perm (Fin (2 * n))) :
    (0 : Fin (n + 1)) ∈ recBoundaries w := by
  simp only [recBoundaries, Set.mem_toFinset, Set.mem_setOf_eq]
  rcases Nat.eq_zero_or_pos n with h | h
  · left; simpa using h.symm
  · right; refine ⟨by simpa using h, ?_⟩
    intro j hj; simp at hj

lemma recBoundaries_last_mem (w : Equiv.Perm (Fin (2 * n))) :
    Fin.last n ∈ recBoundaries w := by
  simp only [recBoundaries, Set.mem_toFinset, Set.mem_setOf_eq]; left; simp

/-- The record composition packaged as a `CompositionAsSet`. -/
def rcAsSet (w : Equiv.Perm (Fin (2 * n))) : CompositionAsSet n where
  boundaries := recBoundaries w
  zero_mem := recBoundaries_zero_mem w
  getLast_mem := recBoundaries_last_mem w

/-- The record composition `rc(ŵ)` (Definition 6). -/
def rc (w : Equiv.Perm (Fin (2 * n))) : Composition n := (rcAsSet w).toComposition

/-- The counting function `N(α)` (Definition 7). -/
def N {n : ℕ} (α : Composition n) : ℕ :=
  ((downUpPerms n).filter (fun w => rc w = α)).card

end Perm

/-! ## Noncommutative symmetric functions and related maps (Definition 8) -/

/-- `NSym`, the free associative unital `K`-algebra on noncommuting generators indexed by
`ℕ`.  The generator `k ≥ 1` represents the noncommutative power sum `Ψ_k`. -/
abbrev NSym (K : Type*) [Field K] := FreeAlgebra K ℕ

/-- `Ψ_k` (`k ≥ 1`) is the free generator; `Ψ_0 := 1`. -/
def Psi (K : Type*) [Field K] (k : ℕ) : NSym K :=
  if k = 0 then 1 else FreeAlgebra.ι K k

/-- `Ψ^α = Ψ_{α_1} Ψ_{α_2} ⋯ Ψ_{α_ℓ}`. -/
def PsiComp (K : Type*) [Field K] {n : ℕ} (α : Composition n) : NSym K :=
  ((α.blocks).map (Psi K)).prod

/-- The complete homogeneous generators `S_n`, defined by `S_0 = 1` and the recursion
`n S_n = ∑_{k=1}^n S_{n-k} Ψ_k` (Definition 8). -/
noncomputable def Sgen (K : Type*) [Field K] : ℕ → NSym K
  | 0 => 1
  | (n + 1) =>
      (n + 1 : K)⁻¹ • ∑ k ∈ Finset.range (n + 1), Sgen K (n - k) * Psi K (k + 1)
  decreasing_by · omega

/-- The algebra endomorphism `φ_b : NSym → NSym` with `φ_b(Ψ_k) = b_k Ψ_k`. -/
noncomputable def phiB (K : Type*) [Field K] [CharZero K] : NSym K →ₐ[K] NSym K :=
  FreeAlgebra.lift K (fun k => ((bRat k : ℚ) : K) • FreeAlgebra.ι K k)

/-- `𝐀_n := φ_b(S_n) ∈ NSym`. -/
noncomputable def Anc (K : Type*) [Field K] [CharZero K] (n : ℕ) : NSym K :=
  phiB K (Sgen K n)

/-- The (commutative) algebra of symmetric functions, modelled as the polynomial ring on
the power sums `p_k = X_k` (which are algebraically independent over a `char 0` field). -/
abbrev SymFn (K : Type*) [Field K] := MvPolynomial ℕ K

/-- The power sum `p_k = X_k`, with `p_0 := 1`. -/
noncomputable def psym (K : Type*) [Field K] (k : ℕ) : SymFn K :=
  if k = 0 then 1 else MvPolynomial.X k

/-- The forgetful algebra homomorphism `χ : NSym → Sym` with `χ(Ψ_k) = p_k` (equivalently
`χ(S_n) = h_n`). -/
noncomputable def chiMap (K : Type*) [Field K] : NSym K →ₐ[K] SymFn K :=
  FreeAlgebra.lift K (fun k => psym K k)

/-- `z_λ = ∏_i i^{m_i} m_i!`, where `m_i` is the multiplicity of `i` in `λ`. -/
def zLam (parts : Multiset ℕ) : ℚ :=
  ∏ i ∈ parts.toFinset, (i : ℚ) ^ (parts.count i) * (Nat.factorial (parts.count i))

/-- `b_λ = ∏_i b_{λ_i}`. -/
def bLam (parts : Multiset ℕ) : ℚ := (parts.map bRat).prod

/-- `p_λ = ∏_i p_{λ_i}`. -/
noncomputable def psymLam (K : Type*) [Field K] (parts : Multiset ℕ) : SymFn K :=
  (parts.map (psym K)).prod

/-- `A_n = ∑_{λ ⊢ n} z_λ^{-1} b_λ p_λ ∈ Sym` (Definition 8). -/
noncomputable def Asym (K : Type*) [Field K] [CharZero K] (n : ℕ) : SymFn K :=
  ∑ lam : Nat.Partition n,
    (((zLam lam.parts)⁻¹ * bLam lam.parts : ℚ) : K) • psymLam K lam.parts

/-! ## The right-hand side of Statement 1 -/

/-- The closed-form product `∏_{j=1}^ℓ C(2 s_j - 1, 2 α_j - 1) E_{2 α_j - 1}`, where
`s_j` is the `j`-th partial sum (`= α.sizeUpTo (i+1)` for the `0`-indexed part `i`). -/
def rhsBinom {n : ℕ} (α : Composition n) : ℕ :=
  ∏ i : Fin α.length,
    Nat.choose (2 * α.sizeUpTo (i + 1) - 1) (2 * α.blocksFun i - 1) *
      euler (2 * α.blocksFun i - 1)

/-- Telescoping product for a nowhere-zero function into a field. -/
theorem prod_range_div_telescope {G : Type*} [Field G] (g : ℕ → G)
    (hg : ∀ j, g j ≠ 0) (m : ℕ) :
    ∏ i ∈ Finset.range m, g (i + 1) / g i = g m / g 0 := by
  induction m with
  | zero => simp [div_self (hg 0)]
  | succ k ih =>
    rw [Finset.prod_range_succ, ih, div_mul_div_comm, mul_comm (g k) (g (k + 1)),
      mul_div_mul_right _ _ (hg k)]

/-- Consistency of the two product forms in Statement 1 (as rationals):
`∏_j C(2 s_j - 1, 2 α_j - 1) E_{2 α_j - 1} = (2n)! ∏_j b_{α_j} / s_j`. -/
theorem rhsBinom_eq_rhsRat {n : ℕ} (hn : 1 ≤ n) (α : Composition n) :
    (rhsBinom α : ℚ)
      = (Nat.factorial (2 * n)) *
          ∏ i : Fin α.length, bRat (α.blocksFun i) / (α.sizeUpTo (i + 1)) := by
  -- abbreviations
  set ℓ := α.length with hℓ
  -- per-factor decomposition: LHS_i = T_i * RHS_i
  have key : ∀ i : Fin ℓ,
      ((Nat.choose (2 * α.sizeUpTo (i + 1) - 1) (2 * α.blocksFun i - 1) *
          euler (2 * α.blocksFun i - 1) : ℕ) : ℚ)
        = ((Nat.factorial (2 * α.sizeUpTo (i + 1)) : ℚ) /
            (Nat.factorial (2 * α.sizeUpTo i) : ℚ))
          * (bRat (α.blocksFun i) / (α.sizeUpTo (i + 1))) := by
    intro i
    have hi : (i : ℕ) < ℓ := i.isLt
    have hsucc : α.sizeUpTo ((i : ℕ) + 1) = α.sizeUpTo i + α.blocksFun i :=
      Composition.sizeUpTo_succ' α i
    set p := α.sizeUpTo (i : ℕ) with hp
    set a := α.blocksFun i with ha
    have ha1 : 1 ≤ a := Composition.one_le_blocksFun α i
    rw [hsucc]
    -- rewrite choose as ratio of factorials
    have hle : 2 * a - 1 ≤ 2 * (p + a) - 1 := by omega
    have hsub : 2 * (p + a) - 1 - (2 * a - 1) = 2 * p := by omega
    rw [Nat.cast_mul, Nat.cast_choose ℚ hle, hsub]
    -- factorial split facts
    have e1 : Nat.factorial (2 * (p + a)) = (2 * (p + a)) * Nat.factorial (2 * (p + a) - 1) :=
      (Nat.mul_factorial_pred (by omega)).symm
    have e2 : Nat.factorial (2 * a) = (2 * a) * Nat.factorial (2 * a - 1) :=
      (Nat.mul_factorial_pred (by omega)).symm
    unfold bRat
    -- now pure field algebra
    have hfp : (Nat.factorial (2 * p) : ℚ) ≠ 0 := by positivity
    have hfa : (Nat.factorial (2 * a - 1) : ℚ) ≠ 0 := by positivity
    have hpa : ((p + a : ℕ) : ℚ) ≠ 0 := by
      have : 0 < p + a := by omega
      positivity
    have h2a : ((2 * a : ℕ) : ℚ) ≠ 0 := by
      have : 0 < 2 * a := by omega
      positivity
    push_cast [e1, e2]
    field_simp
  -- Now conclude.
  unfold rhsBinom
  rw [Nat.cast_prod]
  simp only [key]
  rw [Finset.prod_mul_distrib]
  -- the T-product telescopes to (2n)!
  set g : ℕ → ℚ := fun j => (Nat.factorial (2 * α.sizeUpTo j) : ℚ) with hg
  have hgne : ∀ j, g j ≠ 0 := by
    intro j; simp only [hg]; positivity
  have htele :
      (∏ i : Fin ℓ, (Nat.factorial (2 * α.sizeUpTo (i + 1)) : ℚ) /
          (Nat.factorial (2 * α.sizeUpTo i) : ℚ))
        = (Nat.factorial (2 * n) : ℚ) := by
    have : (∏ i : Fin ℓ, g ((i : ℕ) + 1) / g (i : ℕ))
        = ∏ i ∈ Finset.range ℓ, g (i + 1) / g i := by
      rw [Fin.prod_univ_eq_prod_range (fun j => g (j + 1) / g j) ℓ]
    rw [show (∏ i : Fin ℓ, (Nat.factorial (2 * α.sizeUpTo (i + 1)) : ℚ) /
          (Nat.factorial (2 * α.sizeUpTo i) : ℚ))
        = ∏ i : Fin ℓ, g ((i : ℕ) + 1) / g (i : ℕ) from rfl, this,
      prod_range_div_telescope g hgne ℓ]
    simp only [hg, hℓ, Composition.sizeUpTo_length, Composition.sizeUpTo_zero]
    norm_num
  rw [htele]

/-! ## Main Statement 1 -/

-- (Statements 1: `N_eq_rhsBinom`, `N_eq_rhsRat` are proved further below,
--  after the `compSnoc` / `compInit` composition helpers they depend on.)


/-! ## Statement 2: algebraic scaffolding (sub-lemmas)

The two identities of Statement 2 both flow from a single structural fact: the
`Ψ`-expansion of the generator `S_n`.  From the defining recursion
`n · S_n = ∑_{k=1}^{n} S_{n-k} Ψ_k` one derives (Notes, "Relation between the two
statements"):
  `S_n = ∑_{α ⊨ n} (∏_{j} s_j(α))⁻¹ · Ψ^α`,       where `s_j(α) = α.sizeUpTo (j)`.
Applying the multiplicative maps `φ_b` and `χ` to this expansion, and reading off the
coefficient of each `Ψ^α`, gives Statement 2. -/

/-- The coefficient `(∏_{j=1}^{ℓ} s_j(α))⁻¹` of `Ψ^α` in the `Ψ`-expansion of `S_n`,
as a rational number (`s_j = α.sizeUpTo (j)`, so the product is over the partial sums
`s_1,...,s_ℓ`). -/
def sgenCoeff {n : ℕ} (α : Composition n) : ℚ :=
  ∏ i : Fin α.length, (α.sizeUpTo (i + 1) : ℚ)⁻¹

/-- **Sub-lemma S2.1 (Ψ-expansion of the complete-homogeneous generators).**
`S_n = ∑_{α ⊨ n} (∏_j s_j)⁻¹ • Ψ^α` in `NSym`.

Informal argument (strong induction on `n`).  For `n = 0` both sides are `1` (the empty
composition contributes coefficient `1`).  For `n ≥ 1`, expand the defining recursion
`n S_n = ∑_{k=1}^{n} S_{n-k} Ψ_k`, i.e. `S_n = (1/n) ∑_{k=1}^n S_{n-k} Ψ_k`.  By the
induction hypothesis each `S_{n-k} = ∑_{β ⊨ n-k} (∏_j s_j(β))⁻¹ Ψ^β`.  Prepending `k` to
the composition `β` (i.e. multiplying `Ψ^β · Ψ_k` on the right in the noncommutative
algebra — note the recursion puts `Ψ_k` on the RIGHT, so we *append* `k` as the last
part) gives a bijection between (compositions `β ⊨ n-k`, part `k`) and compositions
`α ⊨ n` whose LAST part is `k`.  Under this bijection the partial sums of `α` are the
partial sums of `β` together with the final sum `s_ℓ(α) = n`, so
`(∏_j s_j(α))⁻¹ = (∏_j s_j(β))⁻¹ · (1/n)`.  Summing over `k = 1,...,n` (equivalently over
the value of the last part) and over `β` reconstructs `∑_{α ⊨ n} (∏ s_j)⁻¹ Ψ^α`, and the
overall factor `1/n` from the recursion matches the `1/n = 1/s_ℓ(α)` produced by the last
partial sum.  [Mathlib: this is a standard NSym fact; here it must be built by hand from
the `Sgen` recursion.  Key API: `Composition` induction by last part, `sizeUpTo_succ`,
`PsiComp` unfolding `((α.blocks).map (Psi K)).prod`. -/

-- Append a single block of size `k+1` to a composition `β` of `m - k`, giving a
-- composition of `m + 1` (for `k ≤ m`).
def compSnoc (m k : ℕ) (hk : k ≤ m) (β : Composition (m - k)) : Composition (m + 1) :=
  { blocks := β.blocks ++ [k + 1]
    blocks_pos := by
      intro i hi
      rcases List.mem_append.mp hi with h | h
      · exact β.blocks_pos h
      · simp only [List.mem_singleton] at h; omega
    blocks_sum := by
      rw [List.sum_append, β.blocks_sum]
      simp only [List.sum_cons, List.sum_nil, add_zero]
      omega }

lemma compSnoc_blocks (m k : ℕ) (hk : k ≤ m) (β : Composition (m - k)) :
    (compSnoc m k hk β).blocks = β.blocks ++ [k + 1] := rfl

/-- PsiComp of the snoc composition. -/
lemma PsiComp_compSnoc (K : Type*) [Field K] (m k : ℕ) (hk : k ≤ m)
    (β : Composition (m - k)) :
    PsiComp K (compSnoc m k hk β) = PsiComp K β * Psi K (k + 1) := by
  unfold PsiComp
  rw [compSnoc_blocks, List.map_append, List.prod_append]
  simp

lemma compSnoc_length (m k : ℕ) (hk : k ≤ m) (β : Composition (m - k)) :
    (compSnoc m k hk β).length = β.length + 1 := by
  show ((compSnoc m k hk β).blocks).length = β.blocks.length + 1
  rw [compSnoc_blocks]; simp

/-- `sizeUpTo` of the snoc composition for indices `≤ β.length`. -/
lemma compSnoc_sizeUpTo_le (m k : ℕ) (hk : k ≤ m) (β : Composition (m - k))
    {i : ℕ} (hi : i ≤ β.length) :
    (compSnoc m k hk β).sizeUpTo i = β.sizeUpTo i := by
  show ((compSnoc m k hk β).blocks.take i).sum = (β.blocks.take i).sum
  rw [compSnoc_blocks,
    List.take_append_of_le_length (by rw [Composition.blocks_length]; exact hi)]

/-- `sizeUpTo` of the snoc composition at the final index. -/
lemma compSnoc_sizeUpTo_last (m k : ℕ) (hk : k ≤ m) (β : Composition (m - k)) :
    (compSnoc m k hk β).sizeUpTo (β.length + 1) = m + 1 := by
  have h : β.length + 1 = (compSnoc m k hk β).length := (compSnoc_length m k hk β).symm
  rw [h, (compSnoc m k hk β).sizeUpTo_length]

/-- The last block value of a composition of `m+1` (which is nonempty) minus one, as a
member of `Finset.range (m+1)`. -/
lemma comp_blocks_ne_nil {m : ℕ} (α : Composition (m + 1)) : α.blocks ≠ [] := by
  intro h
  have := α.blocks_sum
  rw [h] at this; simp at this

/-- The "init" composition obtained by dropping the last block of `α : Composition (m+1)`,
which is a composition of `m - k` where `k+1` is the last block value. -/
def compInit {m : ℕ} (α : Composition (m + 1)) :
    Composition (m - (α.blocks.getLast (comp_blocks_ne_nil α) - 1)) :=
  { blocks := α.blocks.dropLast
    blocks_pos := fun {i} hi => α.blocks_pos (List.dropLast_subset _ hi)
    blocks_sum := by
      have hne := comp_blocks_ne_nil α
      have hlast_pos : 0 < α.blocks.getLast hne :=
        α.blocks_pos (List.getLast_mem hne)
      have hlast_le : α.blocks.getLast hne ≤ m + 1 := by
        have := α.blocks_sum
        have hmem := List.getLast_mem hne
        calc α.blocks.getLast hne ≤ α.blocks.sum := List.single_le_sum
              (fun x hx => Nat.zero_le x) _ hmem
          _ = m + 1 := α.blocks_sum
      have hsplit : α.blocks.dropLast.sum + α.blocks.getLast hne = α.blocks.sum := by
        conv_rhs => rw [← List.dropLast_append_getLast hne]
        rw [List.sum_append]; simp
      rw [α.blocks_sum] at hsplit
      omega }

lemma compInit_blocks {m : ℕ} (α : Composition (m + 1)) :
    (compInit α).blocks = α.blocks.dropLast := rfl

/-- Coefficient of the snoc composition factors as `sgenCoeff β * (m+1)⁻¹`. -/
lemma sgenCoeff_compSnoc (m k : ℕ) (hk : k ≤ m) (β : Composition (m - k)) :
    sgenCoeff (compSnoc m k hk β) = sgenCoeff β * (m + 1 : ℚ)⁻¹ := by
  unfold sgenCoeff
  rw [compSnoc_length]
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    congr 1
    rw [Fin.coe_castSucc, compSnoc_sizeUpTo_le m k hk β (by have := i.isLt; omega)]
  · rw [Fin.val_last, compSnoc_sizeUpTo_last]
    push_cast
    ring_nf

/-- The last block of the snoc composition is `k + 1`. -/
lemma compSnoc_getLast (m k : ℕ) (hk : k ≤ m) (β : Composition (m - k))
    (h : (compSnoc m k hk β).blocks ≠ []) :
    (compSnoc m k hk β).blocks.getLast h = k + 1 := by
  have h2 : (compSnoc m k hk β).blocks.getLast? = some (k + 1) := by
    rw [compSnoc_blocks]
    rw [List.getLast?_append_of_ne_nil _ (by simp)]
    simp
  rw [List.getLast?_eq_getLast_of_ne_nil h] at h2
  exact Option.some.inj h2

/-- The init of a snoc composition recovers `β` (as blocks). -/
lemma compInit_compSnoc_blocks (m k : ℕ) (hk : k ≤ m) (β : Composition (m - k)) :
    (compInit (compSnoc m k hk β)).blocks = β.blocks := by
  rw [compInit_blocks, compSnoc_blocks]
  simp

/-- Snoc of the init composition recovers `α` (as blocks). -/
lemma compSnoc_compInit_blocks {m : ℕ} (α : Composition (m + 1))
    (hk : α.blocks.getLast (comp_blocks_ne_nil α) - 1 ≤ m) :
    (compSnoc m (α.blocks.getLast (comp_blocks_ne_nil α) - 1) hk (compInit α)).blocks
      = α.blocks := by
  rw [compSnoc_blocks, compInit_blocks]
  have hne := comp_blocks_ne_nil α
  have hlast_pos : 0 < α.blocks.getLast hne := α.blocks_pos (List.getLast_mem hne)
  rw [show α.blocks.getLast hne - 1 + 1 = α.blocks.getLast hne by omega]
  exact List.dropLast_append_getLast hne

/-- Two compositions with equal sizes and equal block lists are heterogeneously equal. -/
lemma Composition.heq_of_blocks {a b : ℕ} (c1 : Composition a) (c2 : Composition b)
    (hab : a = b) (hbl : c1.blocks = c2.blocks) : HEq c1 c2 := by
  subst hab
  exact heq_of_eq (Composition.ext hbl)


/-! ### Alternating-permutation foundation for `euler_recurrence`

Following the research note (`research/cannot_close_euler_recurrence_...tex`): we build the
André split-at-the-maximum enumeration.  `euler n` counts up-down (equivalently down-up)
alternating permutations of `Fin n`, via the bridge that `entringer n k` counts down-up
permutations of `Fin (n+1)` whose first value is `k`. -/

/-- `w : Perm (Fin m)` is down-up alternating: `w_0 > w_1 < w_2 > ⋯`. -/
def IsDownUpLen (m : ℕ) (w : Equiv.Perm (Fin m)) : Prop :=
  ∀ j : ℕ, (h : j < m - 1) →
    if Even j then w ⟨j, by omega⟩ > w ⟨j + 1, by omega⟩
    else w ⟨j, by omega⟩ < w ⟨j + 1, by omega⟩

/-- `w : Perm (Fin m)` is up-down alternating: `w_0 < w_1 > w_2 < ⋯`. -/
def IsUpDownLen (m : ℕ) (w : Equiv.Perm (Fin m)) : Prop :=
  ∀ j : ℕ, (h : j < m - 1) →
    if Even j then w ⟨j, by omega⟩ < w ⟨j + 1, by omega⟩
    else w ⟨j, by omega⟩ > w ⟨j + 1, by omega⟩

instance (m : ℕ) (w : Equiv.Perm (Fin m)) : Decidable (IsDownUpLen m w) :=
  Nat.decidableBallLT _ _

instance (m : ℕ) (w : Equiv.Perm (Fin m)) : Decidable (IsUpDownLen m w) :=
  Nat.decidableBallLT _ _

/-- The set of down-up alternating permutations of `Fin m`. -/
def downUpPermsLen (m : ℕ) : Finset (Equiv.Perm (Fin m)) :=
  {w | IsDownUpLen m w}.toFinset

/-- The set of up-down alternating permutations of `Fin m`. -/
def upDownPermsLen (m : ℕ) : Finset (Equiv.Perm (Fin m)) :=
  {w | IsUpDownLen m w}.toFinset

/-- Down-up permutations of `Fin (n+1)` whose first value is `k`. -/
def downUpFirstFin (n : ℕ) (k : Fin (n + 1)) : Finset (Equiv.Perm (Fin (n + 1))) :=
  {w | IsDownUpLen (n + 1) w ∧ w 0 = k}.toFinset

instance (n : ℕ) (k : Fin (n + 1)) :
    DecidablePred (fun w : Equiv.Perm (Fin (n + 1)) => IsDownUpLen (n + 1) w ∧ w 0 = k) :=
  fun w => inferInstanceAs (Decidable (IsDownUpLen (n + 1) w ∧ w 0 = k))

/-- **L2 helper.** Value complement `i ↦ Fin.rev (w i)` reverses every alternating edge,
turning an up-down permutation into a down-up one and vice versa. -/
lemma card_upDown_eq_card_downUp (m : ℕ) :
    (upDownPermsLen m).card = (downUpPermsLen m).card := by
  apply Finset.card_bij'
    (i := fun (w : Equiv.Perm (Fin m)) (_ : w ∈ upDownPermsLen m) => w.trans Fin.revPerm)
    (j := fun (w : Equiv.Perm (Fin m)) (_ : w ∈ downUpPermsLen m) => w.trans Fin.revPerm)
  · -- MapsTo: up-down → down-up
    intro w hw
    simp only [upDownPermsLen, Set.mem_toFinset, Set.mem_setOf_eq] at hw
    simp only [downUpPermsLen, Set.mem_toFinset, Set.mem_setOf_eq]
    intro j h
    have hwj := hw j h
    simp only [Equiv.trans_apply, Fin.revPerm_apply]
    split_ifs at hwj ⊢ with hj
    · exact Fin.rev_lt_rev.mpr hwj
    · exact Fin.rev_lt_rev.mpr hwj
  · -- MapsTo: down-up → up-down
    intro w hw
    simp only [downUpPermsLen, Set.mem_toFinset, Set.mem_setOf_eq] at hw
    simp only [upDownPermsLen, Set.mem_toFinset, Set.mem_setOf_eq]
    intro j h
    have hwj := hw j h
    simp only [Equiv.trans_apply, Fin.revPerm_apply]
    split_ifs at hwj ⊢ with hj
    · exact Fin.rev_lt_rev.mpr hwj
    · exact Fin.rev_lt_rev.mpr hwj
  · -- left_inv
    intro w hw
    ext x
    simp [Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_rev]
  · -- right_inv
    intro w hw
    ext x
    simp [Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_rev]

/-- Up-down permutations of `Fin (n+1)` whose first value is `k`. -/
def upDownFirstFin (n : ℕ) (k : Fin (n + 1)) : Finset (Equiv.Perm (Fin (n + 1))) :=
  {w | IsUpDownLen (n + 1) w ∧ w 0 = k}.toFinset

instance (n : ℕ) (k : Fin (n + 1)) :
    DecidablePred (fun w : Equiv.Perm (Fin (n + 1)) => IsUpDownLen (n + 1) w ∧ w 0 = k) :=
  fun w => inferInstanceAs (Decidable (IsUpDownLen (n + 1) w ∧ w 0 = k))

/-- **Value-complement bijection with fixed first value.**
`card (upDownFirstFin n ⟨k⟩) = card (downUpFirstFin n ⟨n - k⟩)` for `k ≤ n`. -/
lemma card_upDownFirst_eq_downUpFirst_rev (n k : ℕ) (hk : k ≤ n) :
    (upDownFirstFin n ⟨k, by omega⟩).card = (downUpFirstFin n ⟨n - k, by omega⟩).card := by
  apply Finset.card_bij'
    (i := fun (w : Equiv.Perm (Fin (n + 1))) (_ : w ∈ upDownFirstFin n ⟨k, by omega⟩) =>
      w.trans Fin.revPerm)
    (j := fun (w : Equiv.Perm (Fin (n + 1))) (_ : w ∈ downUpFirstFin n ⟨n - k, by omega⟩) =>
      w.trans Fin.revPerm)
  case hi => -- MapsTo: up-down first k → down-up first (n-k)
    intro w hw
    simp only [upDownFirstFin, Set.mem_toFinset, Set.mem_setOf_eq] at hw
    simp only [downUpFirstFin, Set.mem_toFinset, Set.mem_setOf_eq]
    obtain ⟨hud, hw0⟩ := hw
    refine ⟨?_, ?_⟩
    · intro j h
      have hwj := hud j h
      simp only [Equiv.trans_apply, Fin.revPerm_apply]
      split_ifs at hwj ⊢ with hj
      · exact Fin.rev_lt_rev.mpr hwj
      · exact Fin.rev_lt_rev.mpr hwj
    · simp only [Equiv.trans_apply, Fin.revPerm_apply, hw0]
      apply Fin.ext
      simp only [Fin.rev]
      omega
  case hj => -- MapsTo: down-up first (n-k) → up-down first k
    intro w hw
    simp only [downUpFirstFin, Set.mem_toFinset, Set.mem_setOf_eq] at hw
    simp only [upDownFirstFin, Set.mem_toFinset, Set.mem_setOf_eq]
    obtain ⟨hdu, hw0⟩ := hw
    refine ⟨?_, ?_⟩
    · intro j h
      have hwj := hdu j h
      simp only [Equiv.trans_apply, Fin.revPerm_apply]
      split_ifs at hwj ⊢ with hj
      · exact Fin.rev_lt_rev.mpr hwj
      · exact Fin.rev_lt_rev.mpr hwj
    · simp only [Equiv.trans_apply, Fin.revPerm_apply, hw0]
      apply Fin.ext
      simp only [Fin.rev]
      omega
  case left_inv =>
    intro w hw
    apply Equiv.ext
    intro x
    simp [Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_rev]
  case right_inv =>
    intro w hw
    apply Equiv.ext
    intro x
    simp [Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_rev]

/-- Insertion of a value `j` at position `0`: from an up-down/down-up perm `v` of
`Fin (n+1)` build a perm `w` of `Fin (n+2)` with `w 0 = j` and standardized tail `v`. -/
def insPerm {n : ℕ} (j : Fin (n + 2)) (v : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm (Fin (n + 2)) :=
  (finSuccEquiv' (0 : Fin (n + 2))).trans
    ((Equiv.optionCongr v).trans (finSuccEquiv' j).symm)

lemma insPerm_zero {n : ℕ} (j : Fin (n + 2)) (v : Equiv.Perm (Fin (n + 1))) :
    insPerm j v 0 = j := by
  simp only [insPerm, Equiv.trans_apply, finSuccEquiv'_at, Equiv.optionCongr_apply,
    Option.map_none]
  rw [Equiv.symm_apply_eq, finSuccEquiv'_at]

lemma insPerm_succ {n : ℕ} (j : Fin (n + 2)) (v : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) :
    insPerm j v i.succ = j.succAbove (v i) := by
  simp only [insPerm, Equiv.trans_apply]
  rw [show i.succ = (0 : Fin (n + 2)).succAbove i by rw [Fin.succAbove_zero]]
  rw [finSuccEquiv'_succAbove]
  simp only [Equiv.optionCongr_apply, Option.map_some]
  rw [finSuccEquiv'_symm_some]

/-- The intermediate finset: up-down perms of `Fin (n+1)` whose first value is `< j`. -/
def upDownLt (n j : ℕ) : Finset (Equiv.Perm (Fin (n + 1))) :=
  {v | IsUpDownLen (n + 1) v ∧ (v 0 : ℕ) < j}.toFinset

instance (n j : ℕ) :
    DecidablePred (fun v : Equiv.Perm (Fin (n + 1)) =>
      IsUpDownLen (n + 1) v ∧ (v 0 : ℕ) < j) :=
  fun v => inferInstanceAs (Decidable (IsUpDownLen (n + 1) v ∧ (v 0 : ℕ) < j))

/-- The deletion map: from a perm `w` of `Fin (n+2)` (with `w 0 = j`) recover `v`. -/
def delPerm {n : ℕ} (j : Fin (n + 2)) (w : Equiv.Perm (Fin (n + 2))) :
    Equiv.Perm (Fin (n + 1)) :=
  Equiv.removeNone
    ((finSuccEquiv' (0 : Fin (n + 2))).symm.trans (w.trans (finSuccEquiv' j)))

lemma delPerm_insPerm {n : ℕ} (j : Fin (n + 2)) (v : Equiv.Perm (Fin (n + 1))) :
    delPerm j (insPerm j v) = v := by
  have : (finSuccEquiv' (0 : Fin (n + 2))).symm.trans
      ((insPerm j v).trans (finSuccEquiv' j)) = Equiv.optionCongr v := by
    apply Equiv.ext
    intro x
    simp only [insPerm, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  simp only [delPerm, this, Equiv.removeNone_optionCongr]

/-- If `w 0 = j` then inserting the deleted perm recovers `w`. -/
lemma insPerm_delPerm {n : ℕ} (j : Fin (n + 2)) (w : Equiv.Perm (Fin (n + 2)))
    (hwj : w 0 = j) :
    insPerm j (delPerm j w) = w := by
  set E : Equiv.Perm (Option (Fin (n + 1))) :=
    (finSuccEquiv' (0 : Fin (n + 2))).symm.trans (w.trans (finSuccEquiv' j)) with hE
  have hEnone : E none = none := by
    simp only [hE, Equiv.trans_apply]
    rw [show (finSuccEquiv' (0 : Fin (n + 2))).symm none = 0 by
      rw [Equiv.symm_apply_eq, finSuccEquiv'_at]]
    rw [hwj, finSuccEquiv'_at]
  have hcongr : (Equiv.removeNone E).optionCongr = E := by
    rw [map_equiv_removeNone E, hEnone, Equiv.swap_self]
    rw [show (Equiv.refl (Option (Fin (n + 1)))) = (1 : Equiv.Perm (Option (Fin (n+1)))) from rfl, one_mul]
  have hdel : delPerm j w = Equiv.removeNone E := by rw [delPerm, hE]
  apply Equiv.ext
  intro x
  rw [hdel]
  simp only [insPerm, Equiv.trans_apply]
  rw [hcongr]
  simp only [hE, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.symm_apply_apply]

/-- Characterization of `w 1` via insertion. -/
lemma insPerm_downUp_iff {n : ℕ} (j : Fin (n + 2)) (v : Equiv.Perm (Fin (n + 1))) :
    IsDownUpLen (n + 2) (insPerm j v)
      ↔ (IsUpDownLen (n + 1) v ∧ ((v 0 : ℕ) < (j : ℕ))) := by
  constructor
  · intro hdu
    refine ⟨?_, ?_⟩
    · -- v is up-down
      intro p hp
      -- edge (p, p+1) of v corresponds to edge (p+1, p+2) of w = insPerm j v
      have hw := hdu (p + 1) (by omega)
      -- w (p+1) = j.succAbove (v ⟨p⟩), w (p+2) = j.succAbove (v ⟨p+1⟩)
      have e1 : (insPerm j v) ⟨p + 1, by omega⟩ = j.succAbove (v ⟨p, by omega⟩) := by
        rw [show (⟨p + 1, by omega⟩ : Fin (n + 2)) = (⟨p, by omega⟩ : Fin (n + 1)).succ by
          apply Fin.ext; simp]
        rw [insPerm_succ]
      have e2 : (insPerm j v) ⟨p + 1 + 1, by omega⟩ = j.succAbove (v ⟨p + 1, by omega⟩) := by
        rw [show (⟨p + 1 + 1, by omega⟩ : Fin (n + 2)) = (⟨p + 1, by omega⟩ : Fin (n + 1)).succ by
          apply Fin.ext; simp]
        rw [insPerm_succ]
      rw [e1, e2] at hw
      -- parity: (p+1) even ↔ p odd
      by_cases hpe : Even p
      · -- p even → want v ⟨p⟩ < v ⟨p+1⟩; p+1 odd → hw : succAbove (v p) < succAbove (v (p+1))
        rw [if_pos hpe]
        have hodd : ¬ Even (p + 1) := by simp [Nat.even_add_one, hpe]
        rw [if_neg hodd] at hw
        exact (Fin.strictMono_succAbove j).lt_iff_lt.mp hw
      · rw [if_neg hpe]
        have heven : Even (p + 1) := by
          rw [Nat.even_add_one]; simpa using hpe
        rw [if_pos heven] at hw
        exact (Fin.strictMono_succAbove j).lt_iff_lt.mp hw
    · -- (v 0 : ℕ) < j
      have hw := hdu 0 (by omega)
      rw [if_pos (show Even (0:ℕ) by decide)] at hw
      rw [show (⟨0, by omega⟩ : Fin (n + 2)) = 0 by rfl, insPerm_zero] at hw
      rw [show (⟨0 + 1, by omega⟩ : Fin (n + 2)) = (0 : Fin (n + 1)).succ by
        apply Fin.ext; simp] at hw
      rw [insPerm_succ] at hw
      -- hw : j > j.succAbove (v 0)
      have : j.succAbove (v 0) < j := hw
      rw [Fin.succAbove_lt_iff_castSucc_lt] at this
      exact this
  · rintro ⟨hud, h0⟩
    intro p hp
    match p, hp with
    | 0, hp =>
      rw [if_pos (show Even (0:ℕ) by decide)]
      rw [show (⟨0, by omega⟩ : Fin (n + 2)) = 0 by rfl, insPerm_zero]
      rw [show (⟨0 + 1, by omega⟩ : Fin (n + 2)) = (0 : Fin (n + 1)).succ by
        apply Fin.ext; simp, insPerm_succ]
      show j.succAbove (v 0) < j
      rw [Fin.succAbove_lt_iff_castSucc_lt]
      rw [Fin.lt_def, Fin.val_castSucc]; exact h0
    | (q + 1), hp =>
      have hq := hud q (by omega)
      have e1 : (insPerm j v) ⟨q + 1, by omega⟩ = j.succAbove (v ⟨q, by omega⟩) := by
        rw [show (⟨q + 1, by omega⟩ : Fin (n + 2)) = (⟨q, by omega⟩ : Fin (n + 1)).succ by
          apply Fin.ext; simp, insPerm_succ]
      have e2 : (insPerm j v) ⟨q + 1 + 1, by omega⟩ = j.succAbove (v ⟨q + 1, by omega⟩) := by
        rw [show (⟨q + 1 + 1, by omega⟩ : Fin (n + 2)) = (⟨q + 1, by omega⟩ : Fin (n + 1)).succ by
          apply Fin.ext; simp, insPerm_succ]
      rw [e1, e2]
      by_cases hqe : Even q
      · have hodd : ¬ Even (q + 1) := by simp [Nat.even_add_one, hqe]
        rw [if_neg hodd]
        rw [if_pos hqe] at hq
        exact (Fin.strictMono_succAbove j).lt_iff_lt.mpr hq
      · have heven : Even (q + 1) := by rw [Nat.even_add_one]; simpa using hqe
        rw [if_pos heven]
        rw [if_neg hqe] at hq
        exact (Fin.strictMono_succAbove j).lt_iff_lt.mpr hq

/-- **The insertion bijection (card form).**
`card(downUpFirstFin (n+1) ⟨j⟩) = card(upDownLt n j)` for `j ≤ n+1`. -/
lemma card_downUpFirst_eq_upDownLt (n j : ℕ) (hj : j ≤ n + 1) :
    (downUpFirstFin (n + 1) ⟨j, by omega⟩).card = (upDownLt n j).card := by
  symm
  apply Finset.card_bij'
    (i := fun (v : Equiv.Perm (Fin (n + 1))) (_ : v ∈ upDownLt n j) =>
      insPerm ⟨j, by omega⟩ v)
    (j := fun (w : Equiv.Perm (Fin (n + 2))) (_ : w ∈ downUpFirstFin (n + 1) ⟨j, by omega⟩) =>
      delPerm ⟨j, by omega⟩ w)
  case hi =>
    intro v hv
    simp only [upDownLt, Set.mem_toFinset, Set.mem_setOf_eq] at hv
    simp only [downUpFirstFin, Set.mem_toFinset, Set.mem_setOf_eq]
    refine ⟨?_, insPerm_zero _ _⟩
    rw [insPerm_downUp_iff]
    exact ⟨hv.1, by simpa using hv.2⟩
  case hj =>
    intro w hw
    simp only [downUpFirstFin, Set.mem_toFinset, Set.mem_setOf_eq] at hw
    simp only [upDownLt, Set.mem_toFinset, Set.mem_setOf_eq]
    obtain ⟨hdu, hw0⟩ := hw
    -- w = insPerm j (delPerm j w) since w 0 = j
    have hins : insPerm ⟨j, by omega⟩ (delPerm ⟨j, by omega⟩ w) = w :=
      insPerm_delPerm ⟨j, by omega⟩ w hw0
    have hdu' := hdu
    rw [← hins, insPerm_downUp_iff] at hdu'
    exact ⟨hdu'.1, by simpa using hdu'.2⟩
  case left_inv =>
    intro v hv
    exact delPerm_insPerm _ v
  case right_inv =>
    intro w hw
    simp only [downUpFirstFin, Set.mem_toFinset, Set.mem_setOf_eq] at hw
    obtain ⟨hdu, hw0⟩ := hw
    exact insPerm_delPerm ⟨j, by omega⟩ w hw0

/-- **Peel bijection (Entringer boustrophedon step).**
Deleting position `0` (a peak) from a down-up permutation of `Fin (n+2)` with first
value `k+1` and standardizing the remaining values yields an up-down permutation of
`Fin (n+1)`; its first value ranges over `{0,...,k}`.  This produces the recurrence
`d(n+1,k+1) = d(n+1,k) + u(n,k)`. -/
lemma card_downUpFirst_succ_peel (n k : ℕ) (hk : k ≤ n) :
    (downUpFirstFin (n + 1) ⟨k + 1, by omega⟩).card
      = (downUpFirstFin (n + 1) ⟨k, by omega⟩).card
        + (upDownFirstFin n ⟨k, by omega⟩).card := by
  rw [card_downUpFirst_eq_upDownLt n (k + 1) (by omega),
      card_downUpFirst_eq_upDownLt n k (by omega)]
  -- upDownLt n (k+1) = upDownLt n k ∪ upDownFirstFin n ⟨k⟩, disjointly
  have hdisj : Disjoint (upDownLt n k) (upDownFirstFin n ⟨k, by omega⟩) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [upDownLt, upDownFirstFin, Set.mem_toFinset, Set.mem_setOf_eq] at hv hv'
    have : (v 0 : ℕ) = k := by rw [hv'.2]
    omega
  have hunion : upDownLt n (k + 1)
      = upDownLt n k ∪ upDownFirstFin n ⟨k, by omega⟩ := by
    ext v
    simp only [upDownLt, upDownFirstFin, Finset.mem_union, Set.mem_toFinset, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hud, hlt⟩
      rcases Nat.lt_or_ge (v 0 : ℕ) k with h | h
      · exact Or.inl ⟨hud, h⟩
      · refine Or.inr ⟨hud, ?_⟩
        apply Fin.ext
        simp only
        omega
    · rintro (⟨hud, hlt⟩ | ⟨hud, heq⟩)
      · exact ⟨hud, by omega⟩
      · refine ⟨hud, ?_⟩
        have : (v 0 : ℕ) = k := by rw [heq]
        omega
  rw [hunion, Finset.card_union_of_disjoint hdisj]

/-- **L1a.** `entringer n k` counts down-up permutations of `Fin (n+1)` with first value `k`. -/
lemma entringer_eq_card_downUpFirst (n k : ℕ) (hk : k ≤ n) :
    entringer n k = (downUpFirstFin n ⟨k, by omega⟩).card := by
  induction n generalizing k with
  | zero =>
    -- n = 0: Fin 1, only the identity, first value 0 = k.
    have hk0 : k = 0 := Nat.le_zero.mp hk
    subst hk0
    show entringer 0 0 = _
    rw [show entringer 0 0 = 1 by simp [entringer]]
    -- there is exactly one permutation of Fin 1
    have : downUpFirstFin 0 ⟨0, by omega⟩ = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro w
      simp only [downUpFirstFin, Set.mem_toFinset, Set.mem_setOf_eq]
      refine ⟨?_, ?_⟩
      · intro j h; omega
      · apply Fin.ext; have := (w 0).isLt; omega
    rw [this]
    rw [Finset.card_univ]
    have : Fintype.card (Equiv.Perm (Fin 1)) = 1 := by decide
    rw [this]
  | succ n IH =>
    -- sub-induction on k
    induction k with
    | zero =>
      -- entringer (n+1) 0 = 0, and no down-up perm of Fin(n+2) has first value 0.
      rw [show entringer (n + 1) 0 = 0 by simp [entringer]]
      symm
      rw [Finset.card_eq_zero]
      rw [Finset.eq_empty_iff_forall_notMem]
      intro w hw
      simp only [downUpFirstFin, Set.mem_toFinset, Set.mem_setOf_eq] at hw
      obtain ⟨hdu, hw0⟩ := hw
      -- position 0 is even, 0 < (n+2)-1, so w 0 > w 1
      have h0 : (0 : ℕ) < (n + 1 + 1) - 1 := by omega
      have := hdu 0 h0
      rw [if_pos (by exact ⟨0, rfl⟩ : Even 0)] at this
      -- w ⟨0⟩ = k = 0, minimal, cannot exceed w 1
      rw [show (⟨0, by omega⟩ : Fin (n + 1 + 1)) = 0 by rfl, hw0] at this
      exact absurd this (by simp [Fin.lt_iff_val_lt_val])
    | succ k IHk =>
      -- Entringer recurrence: entringer (n+1) (k+1) = entringer (n+1) k + entringer n (n-k)
      rw [show entringer (n + 1) (k + 1)
            = entringer (n + 1) k + entringer n (n - k) by
          conv_lhs => rw [entringer]]
      have hkn : k ≤ n := by omega
      rw [IHk (by omega), IH (n - k) (by omega)]
      -- rewrite entringer n (n-k) count via value reversal to upDownFirstFin n ⟨k⟩
      rw [show (downUpFirstFin n ⟨n - k, by omega⟩).card
            = (upDownFirstFin n ⟨k, by omega⟩).card by
          rw [card_upDownFirst_eq_downUpFirst_rev n k hkn]]
      -- now the peel identity
      exact (card_downUpFirst_succ_peel n k hkn).symm

/-- **L1b.** `euler n` counts up-down alternating permutations of `Fin n`. -/
lemma euler_eq_card_upDown (n : ℕ) :
    euler n = (upDownPermsLen n).card := by
  cases n with
  | zero =>
    rw [show euler 0 = 1 by simp [euler, entringer]]
    have : upDownPermsLen 0 = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro w
      simp only [upDownPermsLen, Set.mem_toFinset, Set.mem_setOf_eq]
      intro j h; omega
    rw [this, Finset.card_univ, show Fintype.card (Equiv.Perm (Fin 0)) = 1 by decide]
  | succ m =>
    rw [euler, entringer_eq_card_downUpFirst (m + 1) (m + 1) (le_refl _)]
    rw [card_downUpFirst_eq_upDownLt m (m + 1) (by omega)]
    congr 1
    ext v
    simp only [upDownLt, upDownPermsLen, Set.mem_toFinset, Set.mem_setOf_eq]
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, by have := (v 0).isLt; omega⟩

/-- `euler n` counts down-up alternating permutations of `Fin n`. -/
lemma euler_eq_card_downUp (n : ℕ) :
    euler n = (downUpPermsLen n).card := by
  rw [euler_eq_card_upDown, card_upDown_eq_card_downUp]

/-! ### André split-at-the-maximum sub-lemmas (L4 decomposition)

Bijective proof.  `Φ` sends an alternating permutation `w` of `Fin m` to `(S, ℓ, r)`, where
`p = w.symm (top value)`, `S` = value set of the left segment (positions `< p`), `ℓ` =
standardization of the left segment, `r` = standardization of the right segment.  Parity
dictionary: down-up `w` ⟹ `p` even and `ℓ` down-up; up-down `w` ⟹ `p` odd and `ℓ` up-down;
in both cases `r` is up-down.  Uniting both parities of `w` (LHS = D + U = 2·euler m) matches
summing over `k = p`, with `C(m-1,k)·euler k·euler(m-1-k)`.
-/

/-- **L4-A (max at a peak).** In any permutation of `Fin m`, the maximum value `m-1` sits at
a peak: its immediate neighbours (when they exist) hold strictly smaller values.  This is
immediate from the maximality of `m-1` (the top element of `Fin m`); no alternating
hypothesis is needed. -/
lemma alt_max_at_peak (m : ℕ) (w : Equiv.Perm (Fin m))
    (p : ℕ) (hp : p < m) (hwp : (w ⟨p, hp⟩ : ℕ) = m - 1) :
    (∀ hp1 : p + 1 < m, (w ⟨p + 1, hp1⟩ : ℕ) < m - 1) ∧
    (∀ hp0' : p - 1 < m, 0 < p → (w ⟨p - 1, hp0'⟩ : ℕ) < m - 1) := by
  refine ⟨?_, ?_⟩
  · intro hp1
    have hlt : (w ⟨p + 1, hp1⟩ : ℕ) < m := (w ⟨p + 1, hp1⟩).isLt
    have hne : (w ⟨p + 1, hp1⟩ : ℕ) ≠ m - 1 := by
      intro hval
      have heq : w ⟨p + 1, hp1⟩ = w ⟨p, hp⟩ := by
        apply Fin.ext; rw [hval, hwp]
      have := w.injective heq
      have hpp : p + 1 = p := (Fin.mk.injEq (p + 1) hp1 p hp).mp this
      omega
    omega
  · intro hp0' hp0
    have hlt : (w ⟨p - 1, hp0'⟩ : ℕ) < m := (w ⟨p - 1, hp0'⟩).isLt
    have hne : (w ⟨p - 1, hp0'⟩ : ℕ) ≠ m - 1 := by
      intro hval
      have heq : w ⟨p - 1, hp0'⟩ = w ⟨p, hp⟩ := by
        apply Fin.ext; rw [hval, hwp]
      have := w.injective heq
      have hpp : p - 1 = p := (Fin.mk.injEq (p - 1) hp0' p hp).mp this
      omega
    omega

/-- **L4-B (parity of the max position).** In a down-up permutation of `Fin m`, the maximum
value sits at an even position; in an up-down permutation, at an odd position.  Reason: the
max is a peak (L4-A); a peak at an interior position `p` forces an ascent into `p` and a
descent out of `p`, which — read against the alternating pattern — pins `p`'s parity;
boundary positions `0` / `m-1` are pinned by the first/last step. -/
lemma alt_max_pos_parity (m : ℕ) (hm : 2 ≤ m) (w : Equiv.Perm (Fin m))
    (p : ℕ) (hp : p < m) (hwp : (w ⟨p, hp⟩ : ℕ) = m - 1) :
    (IsDownUpLen m w → Even p) ∧ (IsUpDownLen m w → ¬ Even p) := by
  -- The neighbour values are strictly below the max value m-1.
  have hpeak := alt_max_at_peak m w p hp hwp
  refine ⟨?_, ?_⟩
  · -- down-up: even positions are descents; the ascent INTO p forces p even.
    intro hdu
    by_contra hodd
    -- p is odd and p ≥ 1
    have hp1 : 1 ≤ p := by
      rcases Nat.eq_zero_or_pos p with h | h
      · exact absurd (by rw [h]; decide) hodd
      · exact h
    -- step at j = p-1 : since p-1 is even (p odd), it is a descent: w⟨p-1⟩ > w⟨p⟩.
    have hpe : Even (p - 1) := by
      rcases Nat.even_or_odd p with he | ho
      · exact absurd he hodd
      · rcases ho with ⟨t, ht⟩; exact ⟨t, by omega⟩
    have hjlt : p - 1 < m - 1 := by omega
    have hstep := hdu (p - 1) hjlt
    rw [if_pos hpe] at hstep
    -- hstep : w⟨p-1⟩ > w⟨p-1+1⟩ = w⟨p⟩
    have hidx : (⟨p - 1 + 1, by omega⟩ : Fin m) = ⟨p, hp⟩ := by
      apply Fin.ext; simp; omega
    rw [hidx] at hstep
    -- but w⟨p⟩ is the max, so w⟨p-1⟩ < w⟨p⟩ (values distinct, < m-1)
    have hlt := (hpeak.2 (by omega) (by omega))
    have hval : (w ⟨p, hp⟩ : ℕ) = m - 1 := hwp
    -- w⟨p-1⟩ < m-1 = w⟨p⟩ contradicts w⟨p-1⟩ > w⟨p⟩
    have : (w ⟨p - 1, by omega⟩ : ℕ) < (w ⟨p, hp⟩ : ℕ) := by rw [hval]; exact hlt
    omega
  · -- up-down: even positions are ascents; the max cannot be a peak at an even position.
    intro hud
    by_contra heven
    -- p is even
    rcases Nat.eq_zero_or_pos p with hp0 | hppos
    · -- p = 0: step 0 is an ascent, but w⟨0⟩ is max: contradiction.
      have hjlt : (0 : ℕ) < m - 1 := by omega
      have hstep := hud 0 hjlt
      rw [if_pos (by decide : Even 0)] at hstep
      -- hstep : w⟨0⟩ < w⟨1⟩
      have hidx0 : (⟨0, by omega⟩ : Fin m) = ⟨p, hp⟩ := by apply Fin.ext; simp [hp0]
      rw [hidx0] at hstep
      -- w⟨1⟩ < m-1 = w⟨p⟩, contradiction
      have hlt := hpeak.1 (by omega)
      have hidx1 : (⟨0 + 1, by omega⟩ : Fin m) = ⟨p + 1, by omega⟩ := by
        apply Fin.ext; simp [hp0]
      rw [hidx1] at hstep
      have hval : (w ⟨p, hp⟩ : ℕ) = m - 1 := hwp
      have : (w ⟨p + 1, by omega⟩ : ℕ) < (w ⟨p, hp⟩ : ℕ) := by rw [hval]; exact hlt
      omega
    · -- p even, p ≥ 1: step p-1 (odd) is a descent w⟨p-1⟩ > w⟨p⟩; but w⟨p⟩ max.
      have hpo : ¬ Even (p - 1) := by
        rcases heven with ⟨t, ht⟩
        rw [Nat.not_even_iff_odd]
        exact ⟨t - 1, by omega⟩
      have hjlt : p - 1 < m - 1 := by omega
      have hstep := hud (p - 1) hjlt
      rw [if_neg hpo] at hstep
      have hidx : (⟨p - 1 + 1, by omega⟩ : Fin m) = ⟨p, hp⟩ := by
        apply Fin.ext; simp; omega
      rw [hidx] at hstep
      have hlt := hpeak.2 (by omega) (by omega)
      have hval : (w ⟨p, hp⟩ : ℕ) = m - 1 := hwp
      have : (w ⟨p - 1, by omega⟩ : ℕ) < (w ⟨p, hp⟩ : ℕ) := by rw [hval]; exact hlt
      omega

/-- Number of value-subsets of `Fin m` of a fixed size `k` is `C(m,k)`. -/
lemma card_value_subsets (m k : ℕ) :
    ((Finset.univ : Finset (Fin m)).powersetCard k).card = Nat.choose m k := by
  rw [Finset.card_powersetCard]
  simp

/-- The union of both alternating families of `Fin m`. -/
def altPermsLen (m : ℕ) : Finset (Equiv.Perm (Fin m)) :=
  downUpPermsLen m ∪ upDownPermsLen m

/-- For `m ≥ 2` the down-up and up-down families are disjoint (they disagree at edge 0). -/
lemma disjoint_downUp_upDown (m : ℕ) (hm : 2 ≤ m) :
    Disjoint (downUpPermsLen m) (upDownPermsLen m) := by
  rw [Finset.disjoint_left]
  intro w hdu hud
  simp only [downUpPermsLen, Set.mem_toFinset, Set.mem_setOf_eq] at hdu
  simp only [upDownPermsLen, Set.mem_toFinset, Set.mem_setOf_eq] at hud
  have h0 : (0 : ℕ) < m - 1 := by omega
  have hdu0 := hdu 0 h0
  have hud0 := hud 0 h0
  rw [if_pos (by decide : Even 0)] at hdu0 hud0
  exact absurd hdu0 (by exact not_lt.mpr (le_of_lt hud0))

/-- Cardinality of the combined alternating family: sum of the two parities. -/
lemma card_altPermsLen (m : ℕ) (hm : 2 ≤ m) :
    (altPermsLen m).card = (downUpPermsLen m).card + (upDownPermsLen m).card := by
  rw [altPermsLen, Finset.card_union_of_disjoint (disjoint_downUp_upDown m hm)]

/-- Position of the maximum value `m-1` in a permutation of `Fin m` (for `m ≥ 1`). -/
def posOfMax {m : ℕ} (hm : 1 ≤ m) (w : Equiv.Perm (Fin m)) : ℕ :=
  (w.symm ⟨m - 1, by omega⟩ : Fin m)

lemma posOfMax_lt {m : ℕ} (hm : 1 ≤ m) (w : Equiv.Perm (Fin m)) :
    posOfMax hm w < m := (w.symm ⟨m - 1, by omega⟩).isLt

lemma w_posOfMax {m : ℕ} (hm : 1 ≤ m) (w : Equiv.Perm (Fin m)) :
    (w ⟨posOfMax hm w, posOfMax_lt hm w⟩ : ℕ) = m - 1 := by
  unfold posOfMax
  simp only [Fin.eta, Equiv.apply_symm_apply]

/-- The left-segment target family for the split: down-up if `k` is even, up-down if `k`
is odd.  Its cardinality is `euler k` in either case. -/
def leftAltPerms (k : ℕ) : Finset (Equiv.Perm (Fin k)) :=
  if Even k then downUpPermsLen k else upDownPermsLen k

lemma leftAltPerms_card (k : ℕ) : (leftAltPerms k).card = euler k := by
  unfold leftAltPerms
  split_ifs with h
  · rw [← euler_eq_card_downUp]
  · rw [← euler_eq_card_upDown]

/-- The split data finset: (a `k`-subset `S ⊆ Fin (m-1)` of "left" values) together with a
standardized left alternating perm and a standardized right up-down perm. -/
def splitData (m k : ℕ) :
    Finset ((Finset (Fin (m - 1))) × Equiv.Perm (Fin k) × Equiv.Perm (Fin (m - 1 - k))) :=
  ((Finset.univ : Finset (Fin (m - 1))).powersetCard k) ×ˢ
    (leftAltPerms k) ×ˢ (upDownPermsLen (m - 1 - k))

/-- Cardinality of the split data is the target product `C(m-1,k)·E_k·E_{m-1-k}`. -/
lemma splitData_card (m k : ℕ) :
    (splitData m k).card = Nat.choose (m - 1) k * euler k * euler (m - 1 - k) := by
  unfold splitData
  rw [Finset.card_product, Finset.card_product, card_value_subsets, leftAltPerms_card,
    ← euler_eq_card_upDown, mul_assoc]

/-- Left position embedding `Fin k ↪ Fin m`, `i ↦ i` (positions strictly left of the peak `k`). -/
def leftPos (m k : ℕ) (hk : k < m) (i : Fin k) : Fin m := ⟨i, by omega⟩

/-- Right position embedding `Fin (m-1-k) ↪ Fin m`, `i ↦ k+1+i` (positions right of the peak). -/
def rightPos (m k : ℕ) (hk : k < m) (i : Fin (m - 1 - k)) : Fin m :=
  ⟨k + 1 + i, by have := i.isLt; omega⟩

/-- Totalized "drop the top value" map `Fin m → Fin (m-1)` (for `m ≥ 2`): for `v.val < m-1`
it is the honest embedding `⟨v.val, _⟩`; the top value `m-1` maps to `0`.  On any position
other than the position of the maximum, this is injective / order-preserving. -/
def castDown (m : ℕ) (hm : 2 ≤ m) (v : Fin m) : Fin (m - 1) :=
  if h : (v : ℕ) < m - 1 then ⟨v, h⟩ else ⟨0, by omega⟩

lemma castDown_val {m : ℕ} (hm : 2 ≤ m) {v : Fin m} (h : (v : ℕ) < m - 1) :
    (castDown m hm v : ℕ) = (v : ℕ) := by
  simp only [castDown, dif_pos h]

lemma castDown_lt_iff {m : ℕ} (hm : 2 ≤ m) {v w : Fin m}
    (hv : (v : ℕ) < m - 1) (hw : (w : ℕ) < m - 1) :
    castDown m hm v < castDown m hm w ↔ v < w := by
  simp only [Fin.lt_def, castDown_val hm hv, castDown_val hm hw]

lemma castDown_injOn {m : ℕ} (hm : 2 ≤ m) {v w : Fin m}
    (hv : (v : ℕ) < m - 1) (hw : (w : ℕ) < m - 1)
    (h : castDown m hm v = castDown m hm w) : v = w := by
  apply Fin.ext
  have := congrArg (Fin.val) h
  rwa [castDown_val hm hv, castDown_val hm hw] at this

/-- If a position `pos` is not the position of the maximum, then its value is `< m-1`. -/
lemma nonmax_val_lt {m : ℕ} (hm : 1 ≤ m) (w : Equiv.Perm (Fin m)) (pos : Fin m)
    (hpos : (pos : ℕ) ≠ posOfMax hm w) : (w pos : ℕ) < m - 1 := by
  have hle : (w pos : ℕ) ≤ m - 1 := by have := (w pos).isLt; omega
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · -- (w pos : ℕ) = m - 1, so w pos = w ⟨posOfMax,_⟩, contradiction with injectivity
    exfalso
    have hmax : (w ⟨posOfMax hm w, posOfMax_lt hm w⟩ : ℕ) = m - 1 := w_posOfMax hm w
    have heq : w pos = w ⟨posOfMax hm w, posOfMax_lt hm w⟩ := by
      apply Fin.ext; rw [h, hmax]
    have hpe := w.injective heq
    apply hpos
    have := congrArg (Fin.val) hpe
    simpa using this

/-- Equivalence `Fin j ≃ (univ.image f)` for an injective `f`. -/
noncomputable def toImageEquiv {j N : ℕ} (f : Fin j → Fin N) (hf : Function.Injective f) :
    Fin j ≃ ↥((Finset.univ : Finset (Fin j)).image f) :=
  Equiv.ofBijective
    (fun i => ⟨f i, by simp only [Finset.mem_image]; exact ⟨i, Finset.mem_univ _, rfl⟩⟩)
    (by
      constructor
      · intro a b hab; apply hf; exact Subtype.ext_iff.mp hab
      · rintro ⟨x, hx⟩
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
        obtain ⟨i, rfl⟩ := hx; exact ⟨i, rfl⟩)

lemma toImageEquiv_coe {j N : ℕ} (f : Fin j → Fin N) (hf : Function.Injective f) (i : Fin j) :
    ((toImageEquiv f hf i : _) : Fin N) = f i := rfl

lemma image_card_of_inj {j N : ℕ} (f : Fin j → Fin N) (hf : Function.Injective f) :
    ((Finset.univ : Finset (Fin j)).image f).card = j := by
  rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]

/-- Standardization: the permutation of `Fin j` sending `i` to the rank of `f i`
within the image set of `f`. -/
noncomputable def stdSeg {j N : ℕ} (f : Fin j → Fin N) (hf : Function.Injective f) :
    Equiv.Perm (Fin j) :=
  (toImageEquiv f hf).trans
    (((Finset.univ : Finset (Fin j)).image f).orderIsoOfFin
      (image_card_of_inj f hf)).symm.toEquiv

lemma stdSeg_lt_iff {j N : ℕ} (f : Fin j → Fin N) (hf : Function.Injective f) (a b : Fin j) :
    stdSeg f hf a < stdSeg f hf b ↔ f a < f b := by
  unfold stdSeg
  simp only [Equiv.trans_apply, RelIso.coe_fn_toEquiv]
  rw [((Finset.univ.image f).orderIsoOfFin (image_card_of_inj f hf)).symm.lt_iff_lt]
  show (toImageEquiv f hf a : Fin N) < (toImageEquiv f hf b : Fin N) ↔ f a < f b
  rw [toImageEquiv_coe, toImageEquiv_coe]

/-- The order embedding of the image, composed with `stdSeg`, recovers `f`. -/
lemma stdSeg_orderEmbOfFin {j N : ℕ} (f : Fin j → Fin N) (hf : Function.Injective f)
    (i : Fin j) :
    ((Finset.univ : Finset (Fin j)).image f).orderEmbOfFin (image_card_of_inj f hf)
        (stdSeg f hf i) = f i := by
  rw [← Finset.coe_orderIsoOfFin_apply]
  show (((Finset.univ.image f).orderIsoOfFin (image_card_of_inj f hf))
      (stdSeg f hf i) : Fin N) = f i
  unfold stdSeg
  simp only [Equiv.trans_apply, RelIso.coe_fn_toEquiv, OrderIso.apply_symm_apply]
  show (toImageEquiv f hf i : Fin N) = f i
  rw [toImageEquiv_coe]

/-- `orderEmbOfFin` of any finset equal to `univ.image f`, composed with `stdSeg`,
recovers `f` (the card-equality proof is irrelevant). -/
lemma orderEmbOfFin_stdSeg_of_eq {j N : ℕ} (f : Fin j → Fin N) (hf : Function.Injective f)
    (T : Finset (Fin N)) (hT : T.card = j) (hTeq : T = (Finset.univ : Finset (Fin j)).image f)
    (i : Fin j) :
    T.orderEmbOfFin hT (stdSeg f hf i) = f i := by
  subst hTeq
  rw [← stdSeg_orderEmbOfFin f hf i]

/-- Honest lift `Fin (m-1) → Fin m`. -/
def valLift (m : ℕ) (hm : 2 ≤ m) (v : Fin (m - 1)) : Fin m := ⟨v, by have := v.isLt; omega⟩

lemma valLift_val {m : ℕ} (hm : 2 ≤ m) (v : Fin (m - 1)) :
    (valLift m hm v : ℕ) = (v : ℕ) := rfl

lemma castDown_valLift {m : ℕ} (hm : 2 ≤ m) (v : Fin (m - 1)) :
    castDown m hm (valLift m hm v) = v := by
  apply Fin.ext
  rw [castDown_val hm (by rw [valLift_val]; exact v.isLt)]
  rfl

lemma valLift_castDown {m : ℕ} (hm : 2 ≤ m) {x : Fin m} (hx : (x : ℕ) < m - 1) :
    valLift m hm (castDown m hm x) = x := by
  apply Fin.ext
  rw [valLift_val, castDown_val hm hx]

lemma valLift_lt_iff {m : ℕ} (hm : 2 ≤ m) (v w : Fin (m - 1)) :
    valLift m hm v < valLift m hm w ↔ v < w := by
  simp only [Fin.lt_def, valLift_val]

lemma valLift_injective {m : ℕ} (hm : 2 ≤ m) : Function.Injective (valLift m hm) := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  rwa [valLift_val, valLift_val] at this

lemma valLift_lt_max {m : ℕ} (hm : 2 ≤ m) (v : Fin (m - 1)) :
    (valLift m hm v : ℕ) < m - 1 := by rw [valLift_val]; exact v.isLt

/-- Complement cardinality inside `Fin (m-1)`. -/
lemma compl_card_fin {m k : ℕ} {S : Finset (Fin (m - 1))} (hS : S.card = k) :
    Sᶜ.card = m - 1 - k := by
  rw [Finset.card_compl, Fintype.card_fin, hS]

/-- The raw assembled function `Fin m → Fin m` from split data `(S, ℓ, r)`.
Positions `< k` get the standardized left values (via `S`); position `k` gets the max
value `m-1`; positions `> k` get the standardized right values (via `Sᶜ`). -/
noncomputable def assembleFun (m k : ℕ) (hm : 2 ≤ m) (hk : k < m)
    (S : Finset (Fin (m - 1))) (hS : S.card = k)
    (ℓ : Equiv.Perm (Fin k)) (r : Equiv.Perm (Fin (m - 1 - k)))
    (pos : Fin m) : Fin m :=
  if h1 : (pos : ℕ) < k then
    valLift m hm (S.orderEmbOfFin hS (ℓ ⟨pos, h1⟩))
  else if h2 : (pos : ℕ) = k then
    ⟨m - 1, by omega⟩
  else
    valLift m hm (Sᶜ.orderEmbOfFin (compl_card_fin hS) (r ⟨(pos : ℕ) - k - 1, by
      have := pos.isLt; omega⟩))

lemma assembleFun_left {m k : ℕ} (hm : 2 ≤ m) (hk : k < m)
    {S : Finset (Fin (m - 1))} (hS : S.card = k)
    (ℓ : Equiv.Perm (Fin k)) (r : Equiv.Perm (Fin (m - 1 - k)))
    (pos : Fin m) (h1 : (pos : ℕ) < k) :
    assembleFun m k hm hk S hS ℓ r pos
      = valLift m hm (S.orderEmbOfFin hS (ℓ ⟨pos, h1⟩)) := by
  simp only [assembleFun, dif_pos h1]

lemma assembleFun_mid {m k : ℕ} (hm : 2 ≤ m) (hk : k < m)
    {S : Finset (Fin (m - 1))} (hS : S.card = k)
    (ℓ : Equiv.Perm (Fin k)) (r : Equiv.Perm (Fin (m - 1 - k)))
    (pos : Fin m) (h2 : (pos : ℕ) = k) :
    assembleFun m k hm hk S hS ℓ r pos = ⟨m - 1, by omega⟩ := by
  simp only [assembleFun, dif_neg (by omega : ¬ (pos : ℕ) < k), dif_pos h2]

lemma assembleFun_right {m k : ℕ} (hm : 2 ≤ m) (hk : k < m)
    {S : Finset (Fin (m - 1))} (hS : S.card = k)
    (ℓ : Equiv.Perm (Fin k)) (r : Equiv.Perm (Fin (m - 1 - k)))
    (pos : Fin m) (h3 : k < (pos : ℕ)) :
    assembleFun m k hm hk S hS ℓ r pos
      = valLift m hm (Sᶜ.orderEmbOfFin (compl_card_fin hS) (r ⟨(pos : ℕ) - k - 1, by
          have := pos.isLt; omega⟩)) := by
  simp only [assembleFun, dif_neg (by omega : ¬ (pos : ℕ) < k),
    dif_neg (by omega : ¬ (pos : ℕ) = k)]

lemma assembleFun_injective {m k : ℕ} (hm : 2 ≤ m) (hk : k < m)
    {S : Finset (Fin (m - 1))} (hS : S.card = k)
    (ℓ : Equiv.Perm (Fin k)) (r : Equiv.Perm (Fin (m - 1 - k))) :
    Function.Injective (assembleFun m k hm hk S hS ℓ r) := by
  intro a b hab
  -- value-in-S vs value-in-Sᶜ vs max distinguishes the three regions
  have hSmem : ∀ (p : Fin m) (hp : (p : ℕ) < k),
      assembleFun m k hm hk S hS ℓ r p ∈ (S.image (valLift m hm)) := by
    intro p hp
    rw [assembleFun_left hm hk hS ℓ r p hp]
    rw [Finset.mem_image]
    exact ⟨_, S.orderEmbOfFin_mem hS _, rfl⟩
  have hScmem : ∀ (p : Fin m) (hp : k < (p : ℕ)),
      assembleFun m k hm hk S hS ℓ r p ∈ (Sᶜ.image (valLift m hm)) := by
    intro p hp
    rw [assembleFun_right hm hk hS ℓ r p hp]
    rw [Finset.mem_image]
    exact ⟨_, Sᶜ.orderEmbOfFin_mem (compl_card_fin hS) _, rfl⟩
  have hval_max : ∀ (p : Fin m) (hp : (p : ℕ) = k),
      (assembleFun m k hm hk S hS ℓ r p : ℕ) = m - 1 := by
    intro p hp; rw [assembleFun_mid hm hk hS ℓ r p hp]
  have hval_lt : ∀ (p : Fin m), (p : ℕ) ≠ k →
      (assembleFun m k hm hk S hS ℓ r p : ℕ) < m - 1 := by
    intro p hp
    rcases lt_or_gt_of_ne hp with h | h
    · rw [assembleFun_left hm hk hS ℓ r p h]; exact valLift_lt_max hm _
    · rw [assembleFun_right hm hk hS ℓ r p h]; exact valLift_lt_max hm _
  -- disjointness of image S and image Sᶜ
  have hdisj : Disjoint (S.image (valLift m hm)) (Sᶜ.image (valLift m hm)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_image] at hx hx'
    obtain ⟨v, hv, rfl⟩ := hx
    obtain ⟨w, hw, hwv⟩ := hx'
    have : v = w := valLift_injective hm hwv.symm
    subst this
    exact (Finset.mem_compl.mp hw) hv
  -- Now do case analysis on positions of a, b.
  by_cases ha : (a : ℕ) = k
  · by_cases hb : (b : ℕ) = k
    · exact Fin.ext (by omega)
    · exfalso
      have := hval_max a ha
      have := hval_lt b hb
      omega
  · by_cases hb : (b : ℕ) = k
    · exfalso
      have := hval_max b hb
      have := hval_lt a ha
      omega
    · -- both ≠ k: same region check
      by_cases ha2 : (a : ℕ) < k
      · by_cases hb2 : (b : ℕ) < k
        · -- both left
          rw [assembleFun_left hm hk hS ℓ r a ha2,
            assembleFun_left hm hk hS ℓ r b hb2] at hab
          have h1 := valLift_injective hm hab
          have h2 := (S.orderEmbOfFin hS).injective h1
          have h3 := ℓ.injective h2
          exact Fin.ext (by have := Fin.mk.injEq (a:ℕ) _ (b:ℕ) _ |>.mp h3; omega)
        · -- a left, b right: contradiction via disjoint images
          exfalso
          have hbk : k < (b : ℕ) := by omega
          have hA := hSmem a ha2
          have hB := hScmem b hbk
          rw [hab] at hA
          exact (Finset.disjoint_left.mp hdisj hA hB)
      · -- a right
        have hak : k < (a : ℕ) := by omega
        by_cases hb2 : (b : ℕ) < k
        · exfalso
          have hA := hScmem a hak
          have hB := hSmem b hb2
          rw [hab] at hA
          exact (Finset.disjoint_left.mp hdisj hB hA)
        · -- both right
          have hbk : k < (b : ℕ) := by omega
          rw [assembleFun_right hm hk hS ℓ r a hak,
            assembleFun_right hm hk hS ℓ r b hbk] at hab
          have h1 := valLift_injective hm hab
          have h2 := (Sᶜ.orderEmbOfFin (compl_card_fin hS)).injective h1
          have h3 := r.injective h2
          have h4 : (a : ℕ) - k - 1 = (b : ℕ) - k - 1 :=
            (Fin.mk.injEq _ _ _ _).mp h3
          exact Fin.ext (by omega)

/-- The assembled permutation. -/
noncomputable def assemblePerm (m k : ℕ) (hm : 2 ≤ m) (hk : k < m)
    (S : Finset (Fin (m - 1))) (hS : S.card = k)
    (ℓ : Equiv.Perm (Fin k)) (r : Equiv.Perm (Fin (m - 1 - k))) :
    Equiv.Perm (Fin m) :=
  Equiv.ofBijective (assembleFun m k hm hk S hS ℓ r)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨assembleFun_injective hm hk hS ℓ r, rfl⟩)

lemma assemblePerm_apply (m k : ℕ) (hm : 2 ≤ m) (hk : k < m)
    (S : Finset (Fin (m - 1))) (hS : S.card = k)
    (ℓ : Equiv.Perm (Fin k)) (r : Equiv.Perm (Fin (m - 1 - k))) (pos : Fin m) :
    assemblePerm m k hm hk S hS ℓ r pos = assembleFun m k hm hk S hS ℓ r pos := rfl

/-- Value comparison in the left segment: monotone via `ℓ`. -/
lemma assembleFun_left_lt {m k : ℕ} (hm : 2 ≤ m) (hk : k < m)
    {S : Finset (Fin (m - 1))} (hS : S.card = k)
    (ℓ : Equiv.Perm (Fin k)) (r : Equiv.Perm (Fin (m - 1 - k)))
    {i j : Fin m} (hi : (i : ℕ) < k) (hj : (j : ℕ) < k) :
    assembleFun m k hm hk S hS ℓ r i < assembleFun m k hm hk S hS ℓ r j
      ↔ ℓ ⟨i, hi⟩ < ℓ ⟨j, hj⟩ := by
  rw [assembleFun_left hm hk hS ℓ r i hi, assembleFun_left hm hk hS ℓ r j hj,
    valLift_lt_iff, (S.orderEmbOfFin hS).lt_iff_lt]

/-- Value comparison in the right segment: monotone via `r`. -/
lemma assembleFun_right_lt {m k : ℕ} (hm : 2 ≤ m) (hk : k < m)
    {S : Finset (Fin (m - 1))} (hS : S.card = k)
    (ℓ : Equiv.Perm (Fin k)) (r : Equiv.Perm (Fin (m - 1 - k)))
    {i j : Fin m} (hi : k < (i : ℕ)) (hj : k < (j : ℕ)) :
    assembleFun m k hm hk S hS ℓ r i < assembleFun m k hm hk S hS ℓ r j
      ↔ r ⟨(i : ℕ) - k - 1, by have := i.isLt; omega⟩
          < r ⟨(j : ℕ) - k - 1, by have := j.isLt; omega⟩ := by
  rw [assembleFun_right hm hk hS ℓ r i hi, assembleFun_right hm hk hS ℓ r j hj,
    valLift_lt_iff, (Sᶜ.orderEmbOfFin (compl_card_fin hS)).lt_iff_lt]

/-- The right segment of the assembled perm is always up-down (independent of `k`'s parity):
for a right-region edge, the comparison is dictated by `r`'s up-down pattern with a parity
shift.  This packages the case-D computation. -/
lemma assembleFun_right_edge {m k : ℕ} (hm : 2 ≤ m) (hk : k < m)
    {S : Finset (Fin (m - 1))} (hS : S.card = k)
    (ℓ : Equiv.Perm (Fin k)) (r : Equiv.Perm (Fin (m - 1 - k)))
    (hr : IsUpDownLen (m - 1 - k) r)
    (j : ℕ) (hj : j < m - 1) (hjk : k < j) :
    (assembleFun m k hm hk S hS ℓ r ⟨j, by omega⟩
        < assembleFun m k hm hk S hS ℓ r ⟨j + 1, by omega⟩)
      ↔ Even (j - k - 1) := by
  set t := j - k - 1 with ht
  have htlt : t < (m - 1 - k) - 1 := by omega
  have hcmp := assembleFun_right_lt hm hk hS ℓ r (i := (⟨j, by omega⟩ : Fin m))
    (j := (⟨j + 1, by omega⟩ : Fin m)) (by simpa using hjk) (by simp; omega)
  have hidx1 : ((⟨j, by omega⟩ : Fin m) : ℕ) - k - 1 = t := by simp [ht]
  have hidx2 : ((⟨j + 1, by omega⟩ : Fin m) : ℕ) - k - 1 = t + 1 := by simp; omega
  rw [hcmp]
  have he1 : (⟨((⟨j, by omega⟩ : Fin m) : ℕ) - k - 1, by
      have := (⟨j, by omega⟩ : Fin m).isLt; omega⟩ : Fin (m - 1 - k))
      = ⟨t, by omega⟩ := by apply Fin.ext; exact hidx1
  have he2 : (⟨((⟨j + 1, by omega⟩ : Fin m) : ℕ) - k - 1, by
      have := (⟨j + 1, by omega⟩ : Fin m).isLt; omega⟩ : Fin (m - 1 - k))
      = ⟨t + 1, by omega⟩ := by apply Fin.ext; exact hidx2
  rw [he1, he2]
  have hrt := hr t htlt
  have heq1 : (⟨t, by omega⟩ : Fin (m - 1 - k)) = ⟨t, by omega⟩ := rfl
  by_cases hpar : Even t
  · rw [if_pos hpar] at hrt
    constructor
    · intro _; exact hpar
    · intro _; exact hrt
  · rw [if_neg hpar] at hrt
    constructor
    · intro hlt
      exact absurd (lt_trans hlt hrt) (lt_irrefl _)
    · intro hcon; exact absurd hcon hpar

/-- The assembled perm has value `m-1` at position `k`. -/
lemma assemblePerm_at_k (m k : ℕ) (hm : 2 ≤ m) (hk : k < m)
    (S : Finset (Fin (m - 1))) (hS : S.card = k)
    (ℓ : Equiv.Perm (Fin k)) (r : Equiv.Perm (Fin (m - 1 - k))) :
    (assemblePerm m k hm hk S hS ℓ r ⟨k, hk⟩ : ℕ) = m - 1 := by
  rw [assemblePerm_apply, assembleFun_mid hm hk hS ℓ r ⟨k, hk⟩ rfl]

/-- Position of the max value in the assembled perm is `k`. -/
lemma posOfMax_assemblePerm (m k : ℕ) (hm : 2 ≤ m) (hk : k < m)
    (S : Finset (Fin (m - 1))) (hS : S.card = k)
    (ℓ : Equiv.Perm (Fin k)) (r : Equiv.Perm (Fin (m - 1 - k))) :
    posOfMax (by omega) (assemblePerm m k hm hk S hS ℓ r) = k := by
  unfold posOfMax
  have hval : assemblePerm m k hm hk S hS ℓ r ⟨k, hk⟩ = ⟨m - 1, by omega⟩ :=
    Fin.ext (assemblePerm_at_k m k hm hk S hS ℓ r)
  have : (assemblePerm m k hm hk S hS ℓ r).symm ⟨m - 1, by omega⟩ = ⟨k, hk⟩ := by
    rw [← hval, Equiv.symm_apply_apply]
  rw [this]

/-! ### Disassemble map (forward direction of the fiber bijection)

Given `w` in the fiber (`posOfMax w = k`), we read off:
* `leftVal w i := castDown (w (leftPos i))`  for `i : Fin k`,
* `rightVal w i := castDown (w (rightPos i))` for `i : Fin (m-1-k)`,
both landing in `Fin (m-1)` (honest, since off the peak all values are `< m-1`).
The left value set is `S := univ.image (leftVal w)`, and the standardized
segments are `ℓ := stdSeg (leftVal w)`, `r := stdSeg (rightVal w)`. -/

/-- Left value map of the disassembly. -/
noncomputable def leftVal (m k : ℕ) (hm : 2 ≤ m) (hk : k < m)
    (w : Equiv.Perm (Fin m)) (i : Fin k) : Fin (m - 1) :=
  castDown m hm (w (leftPos m k hk i))

/-- Right value map of the disassembly. -/
noncomputable def rightVal (m k : ℕ) (hm : 2 ≤ m) (hk : k < m)
    (w : Equiv.Perm (Fin m)) (i : Fin (m - 1 - k)) : Fin (m - 1) :=
  castDown m hm (w (rightPos m k hk i))

/-- On the fiber (`posOfMax w = k`) the value at any left position is `< m-1`. -/
lemma leftPos_val_lt {m k : ℕ} (hm : 2 ≤ m) (hk : k < m)
    (w : Equiv.Perm (Fin m)) (hmax : posOfMax (by omega) w = k) (i : Fin k) :
    (w (leftPos m k hk i) : ℕ) < m - 1 := by
  apply nonmax_val_lt (by omega) w (leftPos m k hk i)
  rw [hmax]; simp only [leftPos]; exact Nat.ne_of_lt i.isLt

/-- On the fiber (`posOfMax w = k`) the value at any right position is `< m-1`. -/
lemma rightPos_val_lt {m k : ℕ} (hm : 2 ≤ m) (hk : k < m)
    (w : Equiv.Perm (Fin m)) (hmax : posOfMax (by omega) w = k) (i : Fin (m - 1 - k)) :
    (w (rightPos m k hk i) : ℕ) < m - 1 := by
  apply nonmax_val_lt (by omega) w (rightPos m k hk i)
  rw [hmax]; simp only [rightPos]; have := i.isLt; omega

/-- `leftVal w` is injective (on the fiber). -/
lemma leftVal_injective {m k : ℕ} (hm : 2 ≤ m) (hk : k < m)
    (w : Equiv.Perm (Fin m)) (hmax : posOfMax (by omega) w = k) :
    Function.Injective (leftVal m k hm hk w) := by
  intro a b h
  simp only [leftVal] at h
  have hva := leftPos_val_lt hm hk w hmax a
  have hvb := leftPos_val_lt hm hk w hmax b
  have h2 := castDown_injOn hm hva hvb h
  have h3 := w.injective h2
  simp only [leftPos] at h3
  exact Fin.ext (by have := congrArg Fin.val h3; simpa using this)

/-- `rightVal w` is injective (on the fiber). -/
lemma rightVal_injective {m k : ℕ} (hm : 2 ≤ m) (hk : k < m)
    (w : Equiv.Perm (Fin m)) (hmax : posOfMax (by omega) w = k) :
    Function.Injective (rightVal m k hm hk w) := by
  intro a b h
  simp only [rightVal] at h
  have hva := rightPos_val_lt hm hk w hmax a
  have hvb := rightPos_val_lt hm hk w hmax b
  have h2 := castDown_injOn hm hva hvb h
  have h3 := w.injective h2
  simp only [rightPos, Fin.mk.injEq] at h3
  exact Fin.ext (by omega)

/-- The left value set of the disassembly. -/
noncomputable def leftValSet (m k : ℕ) (hm : 2 ≤ m) (hk : k < m)
    (w : Equiv.Perm (Fin m)) : Finset (Fin (m - 1)) :=
  Finset.univ.image (leftVal m k hm hk w)

/-- The left value set has cardinality `k` (on the fiber). -/
lemma leftValSet_card {m k : ℕ} (hm : 2 ≤ m) (hk : k < m)
    (w : Equiv.Perm (Fin m)) (hmax : posOfMax (by omega) w = k) :
    (leftValSet m k hm hk w).card = k := by
  rw [leftValSet, Finset.card_image_of_injective _ (leftVal_injective hm hk w hmax),
    Finset.card_univ, Fintype.card_fin]

/-- The disassembled left segment permutation. -/
noncomputable def disLeft (m k : ℕ) (hm : 2 ≤ m) (hk : k < m)
    (w : Equiv.Perm (Fin m)) (hmax : posOfMax (by omega) w = k) : Equiv.Perm (Fin k) :=
  stdSeg (leftVal m k hm hk w) (leftVal_injective hm hk w hmax)

/-- The disassembled right segment permutation. -/
noncomputable def disRight (m k : ℕ) (hm : 2 ≤ m) (hk : k < m)
    (w : Equiv.Perm (Fin m)) (hmax : posOfMax (by omega) w = k) :
    Equiv.Perm (Fin (m - 1 - k)) :=
  stdSeg (rightVal m k hm hk w) (rightVal_injective hm hk w hmax)

-- Named obligations for the fiber bijection (proved in the AND branch below):

/-- The right value set is the complement of the left value set (values partition `Fin(m-1)`). -/
lemma disRight_valSet_compl {m k : ℕ} (hm : 2 ≤ m) (hk : k < m)
    (w : Equiv.Perm (Fin m)) (hmax : posOfMax (by omega) w = k) :
    Finset.univ.image (rightVal m k hm hk w) = (leftValSet m k hm hk w)ᶜ := by
  have hsub : Finset.univ.image (rightVal m k hm hk w) ⊆ (leftValSet m k hm hk w)ᶜ := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨j, rfl⟩ := hx
    rw [Finset.mem_compl]
    intro hmem
    simp only [leftValSet, Finset.mem_image, Finset.mem_univ, true_and] at hmem
    obtain ⟨i, hi⟩ := hmem
    simp only [leftVal, rightVal] at hi
    have hvl := leftPos_val_lt hm hk w hmax i
    have hvr := rightPos_val_lt hm hk w hmax j
    have h2 := castDown_injOn hm hvl hvr hi
    have h3 := w.injective h2
    simp only [leftPos, rightPos, Fin.mk.injEq] at h3
    have := i.isLt
    omega
  apply Finset.eq_of_subset_of_card_le hsub
  rw [Finset.card_compl, Fintype.card_fin, leftValSet_card hm hk w hmax,
    Finset.card_image_of_injective _ (rightVal_injective hm hk w hmax),
    Finset.card_univ, Fintype.card_fin]

/-- Forward map lands in `splitData`. -/
lemma disassemble_mem_splitData {m k : ℕ} (hm : 2 ≤ m) (hk : k < m)
    (w : Equiv.Perm (Fin m)) (hw : w ∈ altPermsLen m) (hmax : posOfMax (by omega) w = k) :
    (leftValSet m k hm hk w, disLeft m k hm hk w hmax, disRight m k hm hk w hmax)
      ∈ splitData m k := by
  -- unfold membership in the product
  rw [splitData, Finset.mem_product, Finset.mem_product]
  refine ⟨?_, ?_, ?_⟩
  · -- leftValSet ∈ powersetCard k
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, leftValSet_card hm hk w hmax⟩
  · -- disLeft ∈ leftAltPerms k
    -- Edge comparison: for j, j+1 < k, disLeft edge matches w edge at absolute position j.
    have hedge2 : ∀ (a b : ℕ) (ha : a < k) (hb : b < k),
        (disLeft m k hm hk w hmax ⟨a, ha⟩
            < disLeft m k hm hk w hmax ⟨b, hb⟩)
          ↔ (w ⟨a, by omega⟩ < w ⟨b, by omega⟩) := by
      intro a b ha hb
      rw [disLeft, stdSeg_lt_iff]
      simp only [leftVal]
      rw [castDown_lt_iff hm (leftPos_val_lt hm hk w hmax _)
        (leftPos_val_lt hm hk w hmax _)]
      have e1 : (leftPos m k hk ⟨a, ha⟩ : Fin m) = ⟨a, by omega⟩ := rfl
      have e2 : (leftPos m k hk ⟨b, hb⟩ : Fin m) = ⟨b, by omega⟩ := rfl
      rw [e1, e2]
    have hedge : ∀ j : ℕ, (hj : j < k - 1) →
        (disLeft m k hm hk w hmax ⟨j, by omega⟩
            < disLeft m k hm hk w hmax ⟨j + 1, by omega⟩)
          ↔ (w ⟨j, by omega⟩ < w ⟨j + 1, by omega⟩) :=
      fun j hj => hedge2 j (j+1) (by omega) (by omega)
    rw [leftAltPerms]
    -- split on parity of k using alt_max_pos_parity
    have hpos : (w ⟨k, hk⟩ : ℕ) = m - 1 := by
      have hpk : (w ⟨posOfMax (by omega) w, posOfMax_lt (by omega) w⟩ : ℕ) = m - 1 :=
        w_posOfMax (by omega) w
      have hkeq : (⟨k, hk⟩ : Fin m)
          = ⟨posOfMax (by omega) w, posOfMax_lt (by omega) w⟩ := by
        apply Fin.ext; simp only [Fin.val_mk]; omega
      rw [hkeq]; exact hpk
    have hpar := alt_max_pos_parity m hm w k hk hpos
    rw [altPermsLen, Finset.mem_union] at hw
    split_ifs with hEvenk
    · -- k even ⟹ w is down-up ; disLeft is down-up
      rcases hw with hdu | hud
      · simp only [downUpPermsLen, Set.mem_toFinset, Set.mem_setOf_eq] at hdu ⊢
        intro j hj
        have hwj := hdu j (by omega)
        by_cases hje : Even j
        · rw [if_pos hje]; rw [if_pos hje] at hwj
          change w ⟨j+1, by omega⟩ < w ⟨j, by omega⟩ at hwj
          show disLeft m k hm hk w hmax ⟨j+1, by omega⟩ < disLeft m k hm hk w hmax ⟨j, by omega⟩
          rw [hedge2 (j+1) j (by omega) (by omega)]; exact hwj
        · rw [if_neg hje]; rw [if_neg hje] at hwj
          rw [hedge j (by omega)]; exact hwj
      · exfalso
        simp only [upDownPermsLen, Set.mem_toFinset, Set.mem_setOf_eq] at hud
        exact (hpar.2 hud) hEvenk
    · -- k odd ⟹ w is up-down ; disLeft is up-down
      rcases hw with hdu | hud
      · exfalso
        simp only [downUpPermsLen, Set.mem_toFinset, Set.mem_setOf_eq] at hdu
        exact hEvenk (hpar.1 hdu)
      · simp only [upDownPermsLen, Set.mem_toFinset, Set.mem_setOf_eq] at hud ⊢
        intro j hj
        have hwj := hud j (by omega)
        by_cases hje : Even j
        · rw [if_pos hje]; rw [if_pos hje] at hwj
          rw [hedge j (by omega)]; exact hwj
        · rw [if_neg hje]; rw [if_neg hje] at hwj
          change w ⟨j+1, by omega⟩ < w ⟨j, by omega⟩ at hwj
          show disLeft m k hm hk w hmax ⟨j+1, by omega⟩ < disLeft m k hm hk w hmax ⟨j, by omega⟩
          rw [hedge2 (j+1) j (by omega) (by omega)]; exact hwj
  · -- disRight ∈ upDownPermsLen (m-1-k)
    have hedge2 : ∀ (a b : ℕ) (ha : a < m - 1 - k) (hb : b < m - 1 - k),
        (disRight m k hm hk w hmax ⟨a, ha⟩
            < disRight m k hm hk w hmax ⟨b, hb⟩)
          ↔ (w ⟨k + 1 + a, by omega⟩ < w ⟨k + 1 + b, by omega⟩) := by
      intro a b ha hb
      rw [disRight, stdSeg_lt_iff]
      simp only [rightVal]
      rw [castDown_lt_iff hm (rightPos_val_lt hm hk w hmax _)
        (rightPos_val_lt hm hk w hmax _)]
      have h1 : (rightPos m k hk ⟨a, ha⟩ : Fin m) = ⟨k + 1 + a, by omega⟩ := by
        apply Fin.ext; simp only [rightPos]
      have h2 : (rightPos m k hk ⟨b, hb⟩ : Fin m)
          = ⟨k + 1 + b, by omega⟩ := by
        apply Fin.ext; simp only [rightPos]
      rw [h1, h2]
    have hedge : ∀ t : ℕ, (ht : t < (m - 1 - k) - 1) →
        (disRight m k hm hk w hmax ⟨t, by omega⟩
            < disRight m k hm hk w hmax ⟨t + 1, by omega⟩)
          ↔ (w ⟨k + 1 + t, by omega⟩ < w ⟨k + 1 + (t + 1), by omega⟩) :=
      fun t ht => hedge2 t (t+1) (by omega) (by omega)
    have hpos : (w ⟨k, hk⟩ : ℕ) = m - 1 := by
      have hpk : (w ⟨posOfMax (by omega) w, posOfMax_lt (by omega) w⟩ : ℕ) = m - 1 :=
        w_posOfMax (by omega) w
      have hkeq : (⟨k, hk⟩ : Fin m)
          = ⟨posOfMax (by omega) w, posOfMax_lt (by omega) w⟩ := by
        apply Fin.ext; simp only [Fin.val_mk]; omega
      rw [hkeq]; exact hpk
    have hpar := alt_max_pos_parity m hm w k hk hpos
    rw [altPermsLen, Finset.mem_union] at hw
    simp only [upDownPermsLen, Set.mem_toFinset, Set.mem_setOf_eq]
    intro t ht
    rcases hw with hdu | hud
    · -- w down-up ⟹ k even
      have hEvenk : Even k := hpar.1
        (by simpa only [downUpPermsLen, Set.mem_toFinset, Set.mem_setOf_eq] using hdu)
      simp only [downUpPermsLen, Set.mem_toFinset, Set.mem_setOf_eq] at hdu
      have hwedge := hdu (k + 1 + t) (by omega)
      by_cases hte : Even t
      · rw [if_pos hte, hedge t ht]
        have hjodd : ¬ Even (k + 1 + t) := by
          rcases hEvenk with ⟨a, ha⟩; rcases hte with ⟨b, hb⟩
          rw [Nat.not_even_iff_odd]; exact ⟨a + b, by omega⟩
        rw [if_neg hjodd] at hwedge; exact hwedge
      · rw [if_neg hte]
        have hjeven : Even (k + 1 + t) := by
          rcases hEvenk with ⟨a, ha⟩
          rw [Nat.not_even_iff_odd] at hte; rcases hte with ⟨b, hb⟩
          exact ⟨a + b + 1, by omega⟩
        rw [if_pos hjeven] at hwedge
        change w ⟨k+1+(t+1), by omega⟩ < w ⟨k+1+t, by omega⟩ at hwedge
        show disRight m k hm hk w hmax ⟨t+1, by omega⟩ < disRight m k hm hk w hmax ⟨t, by omega⟩
        rw [hedge2 (t+1) t (by omega) (by omega)]; exact hwedge
    · -- w up-down ⟹ k odd
      have hOddk : ¬ Even k := hpar.2
        (by simpa only [upDownPermsLen, Set.mem_toFinset, Set.mem_setOf_eq] using hud)
      simp only [upDownPermsLen, Set.mem_toFinset, Set.mem_setOf_eq] at hud
      have hwedge := hud (k + 1 + t) (by omega)
      rw [Nat.not_even_iff_odd] at hOddk
      by_cases hte : Even t
      · rw [if_pos hte, hedge t ht]
        have hjeven : Even (k + 1 + t) := by
          rcases hOddk with ⟨a, ha⟩; rcases hte with ⟨b, hb⟩
          exact ⟨a + b + 1, by omega⟩
        rw [if_pos hjeven] at hwedge; exact hwedge
      · rw [if_neg hte]
        have hjodd : ¬ Even (k + 1 + t) := by
          rcases hOddk with ⟨a, ha⟩
          rw [Nat.not_even_iff_odd] at hte; rcases hte with ⟨b, hb⟩
          rw [Nat.not_even_iff_odd]; exact ⟨a + b + 1, by omega⟩
        rw [if_neg hjodd] at hwedge
        change w ⟨k+1+(t+1), by omega⟩ < w ⟨k+1+t, by omega⟩ at hwedge
        show disRight m k hm hk w hmax ⟨t+1, by omega⟩ < disRight m k hm hk w hmax ⟨t, by omega⟩
        rw [hedge2 (t+1) t (by omega) (by omega)]; exact hwedge

/-- Reassembling the disassembly of a fiber element recovers `w`. -/
lemma assemble_disassemble {m k : ℕ} (hm : 2 ≤ m) (hk : k < m)
    (w : Equiv.Perm (Fin m)) (hw : w ∈ altPermsLen m) (hmax : posOfMax (by omega) w = k) :
    assemblePerm m k hm hk (leftValSet m k hm hk w) (leftValSet_card hm hk w hmax)
        (disLeft m k hm hk w hmax) (disRight m k hm hk w hmax) = w := by
  set S := leftValSet m k hm hk w with hSdef
  set hS := leftValSet_card hm hk w hmax with hSc
  set ℓ := disLeft m k hm hk w hmax with hℓdef
  set r := disRight m k hm hk w hmax with hrdef
  apply Equiv.ext
  intro pos
  rw [assemblePerm_apply]
  rcases lt_trichotomy (pos : ℕ) k with h1 | h2 | h3
  · -- left region
    rw [assembleFun_left hm hk hS ℓ r pos h1]
    have hoe : S.orderEmbOfFin hS (ℓ ⟨pos, h1⟩) = leftVal m k hm hk w ⟨pos, h1⟩ := by
      rw [hℓdef, disLeft]
      exact orderEmbOfFin_stdSeg_of_eq (leftVal m k hm hk w)
        (leftVal_injective hm hk w hmax) S hS rfl ⟨pos, h1⟩
    rw [hoe, leftVal, valLift_castDown hm (leftPos_val_lt hm hk w hmax ⟨pos, h1⟩)]
    congr 1
  · -- peak
    rw [assembleFun_mid hm hk hS ℓ r pos h2]
    apply Fin.ext
    have hpe : pos = ⟨posOfMax (by omega) w, posOfMax_lt (by omega) w⟩ :=
      Fin.ext (by simp only [Fin.val_mk]; omega)
    have hwval : (w pos : ℕ) = m - 1 := by
      rw [hpe]; exact w_posOfMax (by omega) w
    show m - 1 = (w pos : ℕ)
    rw [hwval]
  · -- right region
    rw [assembleFun_right hm hk hS ℓ r pos h3]
    have hSc' : Sᶜ = Finset.univ.image (rightVal m k hm hk w) := by
      rw [hSdef]; exact (disRight_valSet_compl hm hk w hmax).symm
    set idx : Fin (m - 1 - k) := ⟨(pos : ℕ) - k - 1, by have := pos.isLt; omega⟩ with hidx
    have hoe : Sᶜ.orderEmbOfFin (compl_card_fin hS) (r idx)
        = rightVal m k hm hk w idx := by
      rw [hrdef, disRight]
      exact orderEmbOfFin_stdSeg_of_eq (rightVal m k hm hk w)
        (rightVal_injective hm hk w hmax) Sᶜ (compl_card_fin hS) hSc' idx
    rw [hoe, rightVal, valLift_castDown hm (rightPos_val_lt hm hk w hmax idx)]
    congr 1
    apply Fin.ext
    simp only [rightPos, hidx]
    omega

/-- The assembled permutation lies in the fiber (alternating). -/
lemma assemblePerm_mem_fiber {m k : ℕ} (hm : 2 ≤ m) (hk : k < m)
    (S : Finset (Fin (m - 1))) (hS : S.card = k)
    (ℓ : Equiv.Perm (Fin k)) (r : Equiv.Perm (Fin (m - 1 - k)))
    (hℓ : ℓ ∈ leftAltPerms k) (hr : r ∈ upDownPermsLen (m - 1 - k)) :
    assemblePerm m k hm hk S hS ℓ r ∈ altPermsLen m := by
  set W := assemblePerm m k hm hk S hS ℓ r with hWdef
  have hrud : IsUpDownLen (m - 1 - k) r := by
    simpa only [upDownPermsLen, Set.mem_toFinset, Set.mem_setOf_eq] using hr
  have hval_max : (W ⟨k, hk⟩ : ℕ) = m - 1 := assemblePerm_at_k m k hm hk S hS ℓ r
  have hval_lt : ∀ p : Fin m, (p : ℕ) ≠ k → (W p : ℕ) < m - 1 := by
    intro p hp
    rw [hWdef, assemblePerm_apply]
    rcases lt_or_gt_of_ne hp with h | h
    · rw [assembleFun_left hm hk hS ℓ r p h]; exact valLift_lt_max hm _
    · rw [assembleFun_right hm hk hS ℓ r p h]; exact valLift_lt_max hm _
  have hleft_lt : ∀ (a b : ℕ) (ha : a < k) (hb : b < k),
      (W ⟨a, by omega⟩ < W ⟨b, by omega⟩) ↔ (ℓ ⟨a, ha⟩ < ℓ ⟨b, hb⟩) := by
    intro a b ha hb
    have := assembleFun_left_lt hm hk hS ℓ r (i := (⟨a, by omega⟩ : Fin m))
      (j := (⟨b, by omega⟩ : Fin m)) (by simpa using ha) (by simpa using hb)
    rw [hWdef, assemblePerm_apply, assemblePerm_apply]
    convert this using 3 <;> simp
  have hright_edge : ∀ (j : ℕ) (hj : j < m - 1) (hjk : k < j),
      (W ⟨j, by omega⟩ < W ⟨j + 1, by omega⟩) ↔ Even (j - k - 1) := by
    intro j hj hjk
    rw [hWdef, assemblePerm_apply, assemblePerm_apply]
    exact assembleFun_right_edge hm hk hS ℓ r hrud j hj hjk
  have hdesc : ∀ (j : ℕ) (hj : j < m - 1),
      ¬ (W ⟨j, by omega⟩ < W ⟨j + 1, by omega⟩) →
        W ⟨j + 1, by omega⟩ < W ⟨j, by omega⟩ := by
    intro j hj hn
    have hne : ((⟨j, by omega⟩ : Fin m)) ≠ ⟨j + 1, by omega⟩ := by
      intro h; have := Fin.val_eq_of_eq h; simp at this
    have hvne : W ⟨j, by omega⟩ ≠ W ⟨j + 1, by omega⟩ := fun h => hne (W.injective h)
    exact lt_of_le_of_ne (not_lt.mp hn) (Ne.symm hvne)
  -- Peak-into edge: position j = k-1, W⟨j+1⟩ = max, so ascent always holds.
  have hpeak_into : ∀ (j : ℕ) (hj : j < m - 1) (heq : j + 1 = k),
      W ⟨j, by omega⟩ < W ⟨j + 1, by omega⟩ := by
    intro j hj heq
    have hj1eq : (⟨j + 1, by omega⟩ : Fin m) = ⟨k, hk⟩ := by apply Fin.ext; omega
    rw [hj1eq, Fin.lt_def, hval_max]
    have hne : ((⟨j, by omega⟩ : Fin m) : ℕ) ≠ k := by simp only [Fin.val_mk]; omega
    have h1 := hval_lt ⟨j, by omega⟩ hne
    simpa using h1
  -- Peak-out edge: position j = k, W⟨j⟩ = max, so descent always holds.
  have hpeak_out : ∀ (j : ℕ) (hj : j < m - 1) (heq : j = k),
      W ⟨j + 1, by omega⟩ < W ⟨j, by omega⟩ := by
    intro j hj heq
    have hjeq : (⟨j, by omega⟩ : Fin m) = ⟨k, hk⟩ := by apply Fin.ext; omega
    rw [hjeq, Fin.lt_def, hval_max]
    have hne : ((⟨j + 1, by omega⟩ : Fin m) : ℕ) ≠ k := by simp only [Fin.val_mk]; omega
    have h1 := hval_lt ⟨j + 1, by omega⟩ hne
    simpa using h1
  rw [altPermsLen, Finset.mem_union]
  by_cases hkpar : Even k
  · have hℓdu : IsDownUpLen k ℓ := by
      have : ℓ ∈ downUpPermsLen k := by
        rw [leftAltPerms, if_pos hkpar] at hℓ; exact hℓ
      simpa only [downUpPermsLen, Set.mem_toFinset, Set.mem_setOf_eq] using this
    left
    simp only [downUpPermsLen, Set.mem_toFinset, Set.mem_setOf_eq]
    intro j hj
    rcases lt_trichotomy (j + 1) k with hlt | heq | hgt
    · have hjk : j < k := by omega
      have hj1k : j + 1 < k := hlt
      have hℓj := hℓdu j (by omega)
      by_cases hpe : Even j
      · rw [if_pos hpe] at hℓj ⊢
        rw [gt_iff_lt] at hℓj ⊢
        have := (hleft_lt (j + 1) j hj1k hjk).mpr (by simpa using hℓj)
        convert this using 2 <;> simp
      · rw [if_neg hpe] at hℓj ⊢
        have := (hleft_lt j (j + 1) hjk hj1k).mpr (by simpa using hℓj)
        convert this using 2 <;> simp
    · -- j+1 = k, k even ⟹ j odd ⟹ down-up needs ascent, holds via peak
      have hpe : ¬ Even j := by
        rcases hkpar with ⟨t, ht⟩; rw [Nat.not_even_iff_odd]; exact ⟨t - 1, by omega⟩
      rw [if_neg hpe]; exact hpeak_into j hj heq
    · rcases Nat.lt_or_ge k j with hkj | hjk
      · -- right region k < j
        by_cases hpe : Even j
        · rw [if_pos hpe, gt_iff_lt]
          apply hdesc j hj
          rw [hright_edge j hj hkj]
          have hpar : Even (j - k - 1) ↔ ¬ Even j := by
            rcases hkpar with ⟨t, ht⟩
            constructor
            · rintro ⟨s, hs⟩ hej; rcases hej with ⟨u, hu⟩; omega
            · intro h; refine ⟨(j - k - 1) / 2, ?_⟩
              rcases Nat.even_or_odd j with he | ho
              · exact absurd he h
              · rcases ho with ⟨u, hu⟩; omega
          rw [hpar]; simpa using hpe
        · rw [if_neg hpe]
          rw [hright_edge j hj hkj]
          have hpar : Even (j - k - 1) ↔ ¬ Even j := by
            rcases hkpar with ⟨t, ht⟩
            constructor
            · rintro ⟨s, hs⟩ hej; rcases hej with ⟨u, hu⟩; omega
            · intro h; refine ⟨(j - k - 1) / 2, ?_⟩
              rcases Nat.even_or_odd j with he | ho
              · exact absurd he h
              · rcases ho with ⟨u, hu⟩; omega
          rw [hpar]; simpa using hpe
      · -- j = k (since k < j+1 and j ≤ k). k even ⟹ j even ⟹ down-up needs descent
        have hjk2 : j = k := by omega
        have hpe : Even j := by rw [hjk2]; exact hkpar
        rw [if_pos hpe, gt_iff_lt]; exact hpeak_out j hj hjk2
  · have hℓud : IsUpDownLen k ℓ := by
      have : ℓ ∈ upDownPermsLen k := by
        rw [leftAltPerms, if_neg hkpar] at hℓ; exact hℓ
      simpa only [upDownPermsLen, Set.mem_toFinset, Set.mem_setOf_eq] using this
    right
    simp only [upDownPermsLen, Set.mem_toFinset, Set.mem_setOf_eq]
    intro j hj
    have hkodd : Odd k := Nat.not_even_iff_odd.mp hkpar
    rcases lt_trichotomy (j + 1) k with hlt | heq | hgt
    · have hjk : j < k := by omega
      have hj1k : j + 1 < k := hlt
      have hℓj := hℓud j (by omega)
      by_cases hpe : Even j
      · rw [if_pos hpe] at hℓj ⊢
        have := (hleft_lt j (j + 1) hjk hj1k).mpr (by simpa using hℓj)
        convert this using 2 <;> simp
      · rw [if_neg hpe] at hℓj ⊢
        rw [gt_iff_lt] at hℓj ⊢
        have := (hleft_lt (j + 1) j hj1k hjk).mpr (by simpa using hℓj)
        convert this using 2 <;> simp
    · -- j+1 = k, k odd ⟹ j even ⟹ up-down needs ascent, holds via peak
      have hpe : Even j := by
        rcases hkodd with ⟨t, ht⟩; exact ⟨t, by omega⟩
      rw [if_pos hpe]; exact hpeak_into j hj heq
    · rcases Nat.lt_or_ge k j with hkj | hjk
      · by_cases hpe : Even j
        · rw [if_pos hpe]
          rw [hright_edge j hj hkj]
          have hpar : Even (j - k - 1) ↔ Even j := by
            rcases hkodd with ⟨t, ht⟩
            constructor
            · rintro ⟨s, hs⟩; exact ⟨s + t + 1, by omega⟩
            · rintro ⟨s, hs⟩; refine ⟨s - t - 1, by omega⟩
          rw [hpar]; exact hpe
        · rw [if_neg hpe, gt_iff_lt]
          apply hdesc j hj
          rw [hright_edge j hj hkj]
          have hpar : Even (j - k - 1) ↔ Even j := by
            rcases hkodd with ⟨t, ht⟩
            constructor
            · rintro ⟨s, hs⟩; exact ⟨s + t + 1, by omega⟩
            · rintro ⟨s, hs⟩; refine ⟨s - t - 1, by omega⟩
          rw [hpar]; simpa using hpe
      · -- j = k, k odd ⟹ j odd ⟹ up-down needs descent
        have hjk2 : j = k := by omega
        have hpe : ¬ Even j := by rw [hjk2, Nat.not_even_iff_odd]; exact hkodd
        rw [if_neg hpe, gt_iff_lt]; exact hpeak_out j hj hjk2

/-- Disassembling the assembly of split data recovers the data. -/
lemma disassemble_assemble {m k : ℕ} (hm : 2 ≤ m) (hk : k < m)
    (S : Finset (Fin (m - 1))) (hS : S.card = k)
    (ℓ : Equiv.Perm (Fin k)) (r : Equiv.Perm (Fin (m - 1 - k)))
    (hℓ : ℓ ∈ leftAltPerms k) (hr : r ∈ upDownPermsLen (m - 1 - k)) :
    (leftValSet m k hm hk (assemblePerm m k hm hk S hS ℓ r),
      disLeft m k hm hk (assemblePerm m k hm hk S hS ℓ r)
        (posOfMax_assemblePerm m k hm hk S hS ℓ r),
      disRight m k hm hk (assemblePerm m k hm hk S hS ℓ r)
        (posOfMax_assemblePerm m k hm hk S hS ℓ r))
      = (S, ℓ, r) := by
  set W := assemblePerm m k hm hk S hS ℓ r with hWdef
  set hmax := posOfMax_assemblePerm m k hm hk S hS ℓ r with hmaxdef
  -- key: leftVal W i = S.orderEmbOfFin hS (ℓ i)
  have hlv : ∀ i : Fin k, leftVal m k hm hk W i = S.orderEmbOfFin hS (ℓ i) := by
    intro i
    have h1 : ((leftPos m k hk i : Fin m) : ℕ) < k := by simp only [leftPos]; exact i.isLt
    rw [leftVal, hWdef, assemblePerm_apply, assembleFun_left hm hk hS ℓ r _ h1]
    rw [castDown_valLift hm]
    congr 2
  -- key: rightVal W j = Sᶜ.orderEmbOfFin (compl_card_fin hS) (r j)
  have hrv : ∀ j : Fin (m - 1 - k),
      rightVal m k hm hk W j = Sᶜ.orderEmbOfFin (compl_card_fin hS) (r j) := by
    intro j
    have h3 : k < ((rightPos m k hk j : Fin m) : ℕ) := by
      simp only [rightPos]; omega
    rw [rightVal, hWdef, assemblePerm_apply, assembleFun_right hm hk hS ℓ r _ h3]
    rw [castDown_valLift hm]
    congr 2
    apply Fin.ext; simp only [rightPos]; omega
  -- component 1: leftValSet W = S
  have hset : leftValSet m k hm hk W = S := by
    rw [leftValSet]
    rw [show (Finset.univ.image (leftVal m k hm hk W))
        = Finset.univ.image (fun i => S.orderEmbOfFin hS (ℓ i)) by
      apply Finset.image_congr; intro i _; exact hlv i]
    rw [show (fun i => S.orderEmbOfFin hS (ℓ i))
        = (fun x => S.orderEmbOfFin hS x) ∘ ℓ from rfl]
    rw [← Finset.image_image, Finset.image_univ_equiv]
    exact Finset.image_orderEmbOfFin_univ S hS
  refine Prod.ext hset (Prod.ext ?_ ?_)
  · -- component 2: disLeft W hmax = ℓ
    show disLeft m k hm hk W hmax = ℓ
    apply Equiv.ext
    intro i
    rw [disLeft]
    have himg : (Finset.univ : Finset (Fin k)).image (leftVal m k hm hk W) = S := hset
    have key : S.orderEmbOfFin hS (stdSeg (leftVal m k hm hk W)
        (leftVal_injective hm hk W hmax) i)
        = leftVal m k hm hk W i :=
      orderEmbOfFin_stdSeg_of_eq (leftVal m k hm hk W)
        (leftVal_injective hm hk W hmax) S hS himg.symm i
    rw [hlv i] at key
    have := (Finset.orderEmbOfFin_eq_orderEmbOfFin_iff (h := hS) (h' := hS)).mp key
    exact Fin.ext this
  · -- component 3: disRight W hmax = r
    show disRight m k hm hk W hmax = r
    apply Equiv.ext
    intro j
    rw [disRight]
    have himg : (Finset.univ : Finset (Fin (m - 1 - k))).image (rightVal m k hm hk W)
        = Sᶜ := by
      rw [disRight_valSet_compl hm hk W hmax, hset]
    have key : Sᶜ.orderEmbOfFin (compl_card_fin hS) (stdSeg (rightVal m k hm hk W)
        (rightVal_injective hm hk W hmax) j)
        = rightVal m k hm hk W j :=
      orderEmbOfFin_stdSeg_of_eq (rightVal m k hm hk W)
        (rightVal_injective hm hk W hmax) Sᶜ (compl_card_fin hS) himg.symm j
    rw [hrv j] at key
    have := (Finset.orderEmbOfFin_eq_orderEmbOfFin_iff
      (h := compl_card_fin hS) (h' := compl_card_fin hS)).mp key
    exact Fin.ext this

/-- **L4-fiber (analytic core).** The number of alternating permutations of `Fin m`
(both parities together) whose maximum value `m-1` sits at position `k` equals
`C(m-1,k) · E_k · E_{m-1-k}`.  This is the André split at a fixed maximum position. -/
lemma altSplit_fiber_card (m k : ℕ) (hm : 2 ≤ m) (hk : k < m) :
    {w ∈ altPermsLen m | posOfMax (by omega) w = k}.card
      = Nat.choose (m - 1) k * euler k * euler (m - 1 - k) := by
  rw [← splitData_card m k]
  apply Finset.card_bij'
    (i := fun w hw => (leftValSet m k hm hk w,
        disLeft m k hm hk w ((Finset.mem_filter.mp hw).2),
        disRight m k hm hk w ((Finset.mem_filter.mp hw).2)))
    (j := fun d hd =>
        assemblePerm m k hm hk d.1 ((Finset.mem_powersetCard.mp
            (Finset.mem_product.mp hd).1).2)
          d.2.1 d.2.2)
  case hi => -- forward lands in splitData
    intro w hw
    exact disassemble_mem_splitData hm hk w (Finset.mem_filter.mp hw).1
      ((Finset.mem_filter.mp hw).2)
  case hj => -- inverse lands in fiber
    intro d hd
    rw [Finset.mem_filter]
    obtain ⟨hd1, hd2⟩ := Finset.mem_product.mp hd
    obtain ⟨hd2a, hd2b⟩ := Finset.mem_product.mp hd2
    refine ⟨?_, ?_⟩
    · exact assemblePerm_mem_fiber hm hk d.1 _ d.2.1 d.2.2 hd2a hd2b
    · exact posOfMax_assemblePerm m k hm hk d.1 _ d.2.1 d.2.2
  case left_inv => -- assemble ∘ disassemble = id
    intro w hw
    exact assemble_disassemble hm hk w (Finset.mem_filter.mp hw).1
      ((Finset.mem_filter.mp hw).2)
  case right_inv => -- disassemble ∘ assemble = id
    intro d hd
    obtain ⟨hd1, hd2⟩ := Finset.mem_product.mp hd
    obtain ⟨hd2a, hd2b⟩ := Finset.mem_product.mp hd2
    exact disassemble_assemble hm hk d.1 _ d.2.1 d.2.2 hd2a hd2b

/-- **L4.** André's split-at-the-maximum: the total number of alternating permutations of
`Fin m` (both parities) is the binomial convolution of Euler numbers. -/
lemma alt_max_split (m : ℕ) (hm : 2 ≤ m) :
    (downUpPermsLen m).card + (upDownPermsLen m).card
      = ∑ k ∈ Finset.range m, Nat.choose (m - 1) k * euler k * euler (m - 1 - k) := by
  rw [← card_altPermsLen m hm]
  -- partition altPermsLen by position of the maximum value
  have hmaps : Set.MapsTo (fun w => posOfMax (by omega : 1 ≤ m) w)
      (↑(altPermsLen m)) (↑(Finset.range m)) := by
    intro w _
    simp only [Finset.coe_range, Set.mem_Iio]
    exact posOfMax_lt (by omega) w
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  exact altSplit_fiber_card m k hm hk

/-- The general zigzag convolution for `m ≥ 2`. -/
lemma euler_recurrence_general (m : ℕ) (hm : 2 ≤ m) :
    2 * euler m
      = ∑ k ∈ Finset.range m, Nat.choose (m - 1) k * euler k * euler (m - 1 - k) := by
  have hsplit := alt_max_split m hm
  have heq := card_upDown_eq_card_downUp m
  rw [euler_eq_card_downUp m, two_mul]
  rw [← hsplit, heq]

/-- `euler` satisfies the standard zigzag recurrence
`2 E_{n+2} = ∑_{k=0}^{n+1} C(n+1, k) E_k E_{n+1-k}`. -/
theorem euler_recurrence (n : ℕ) :
    2 * euler (n + 2)
      = ∑ k ∈ Finset.range (n + 2),
          Nat.choose (n + 1) k * euler k * euler (n + 1 - k) := by
  have h := euler_recurrence_general (n + 2) (by omega)
  simpa using h

/-- The block-split data finset for `N_compSnoc`: a choice of the `2k+1` non-leader values
of the last block (a subset `S` of the `2m+1` values `Fin (2*(m+1)-1)`), a standardized
down-up arrangement of the block tail (length `2k+1`), and a head down-up perm `w'` of
`Fin (2*(m-k))` whose record composition is `β`. -/
def blockSplitData (m k : ℕ) (hk : k ≤ m) (β : Composition (m - k)) :
    Finset ((Finset (Fin (2 * (m + 1) - 1)))
      × Equiv.Perm (Fin (2 * (k + 1) - 1))
      × Equiv.Perm (Fin (2 * (m - k)))) :=
  ((Finset.univ : Finset (Fin (2 * (m + 1) - 1))).powersetCard (2 * (k + 1) - 1))
    ×ˢ (downUpPermsLen (2 * (k + 1) - 1))
    ×ˢ ((downUpPerms (m - k)).filter (fun w' => rc w' = β))

/-- Cardinality of the block-split data equals the target product. -/
lemma blockSplitData_card (m k : ℕ) (hk : k ≤ m) (β : Composition (m - k)) :
    (blockSplitData m k hk β).card
      = Nat.choose (2 * (m + 1) - 1) (2 * (k + 1) - 1)
          * euler (2 * (k + 1) - 1) * N β := by
  unfold blockSplitData
  rw [Finset.card_product, Finset.card_product, card_value_subsets,
    ← euler_eq_card_downUp, mul_assoc]
  rfl

/-- **G1.** `IsDownUp w` (over `Fin (2*n)`) is definitionally the length-`2n` down-up
predicate. -/
lemma isDownUp_iff_isDownUpLen (n : ℕ) (w : Equiv.Perm (Fin (2 * n))) :
    IsDownUp w ↔ IsDownUpLen (2 * n) w := Iff.rfl

/-- **G1'.** The finset of down-up perms `downUpPerms n` (over `Fin (2*n)`) equals
`downUpPermsLen (2*n)`. -/
lemma downUpPerms_eq_downUpPermsLen (n : ℕ) :
    downUpPerms n = downUpPermsLen (2 * n) := by
  unfold downUpPerms downUpPermsLen
  ext w
  simp only [Set.mem_toFinset, Set.mem_setOf_eq]
  exact isDownUp_iff_isDownUpLen n w

/-! ### Last-block split: reusing the generic `assemblePerm`/`disassemble` machinery.

Set `m' := 2*(m+1)` (ground size) and `k' := 2*(m-k)` (block-leader position).  The generic
`assembleFun m' k'` splits `Fin m'` at position `k'`, placing the top value `m'-1 = 2m+1`
(the global maximum) at `k'`; the left segment (positions `< k'`) is the *head* of length
`2*(m-k)`, and the right segment (positions `> k'`) is the *block tail* of length
`m'-1-k' = 2k+1`.  We record the needed record-composition bookkeeping as named lemmas. -/

/-- Position of the block leader (the global maximum) in the last-block split. -/
def leaderPos (m k : ℕ) : ℕ := 2 * (m - k)

lemma leaderPos_lt (m k : ℕ) (hk : k ≤ m) : leaderPos m k < 2 * (m + 1) := by
  unfold leaderPos; omega

/-- The down-up perm of the block tail obtained by reversing the up-down segment
`disRight` (odd length `2k+1`, so its reverse is down-up). -/
noncomputable def blockTailPerm (m k : ℕ) (hk : k ≤ m)
    (w : Equiv.Perm (Fin (2 * (m + 1))))
    (hmax : posOfMax (by omega) w = leaderPos m k) :
    Equiv.Perm (Fin (2 * (m + 1) - 1 - leaderPos m k)) :=
  (disRight (2 * (m + 1)) (leaderPos m k) (by omega) (leaderPos_lt m k hk) w hmax).trans
    Fin.revPerm

/-- **Bridge: record boundaries are exactly the partial sums of `rc w`.**  A position
`i ≤ n` is a record boundary of `w` iff it equals `(rc w).sizeUpTo j` for some `j ≤ length`. -/
lemma recBoundaries_mem_iff (n : ℕ) (w : Equiv.Perm (Fin (2 * n))) (i : ℕ) (hi : i < n + 1) :
    (⟨i, hi⟩ : Fin (n + 1)) ∈ recBoundaries w
      ↔ ∃ j, j ≤ (rc w).length ∧ i = (rc w).sizeUpTo j := by
  have hbdd : (⟨i, hi⟩ : Fin (n + 1)) ∈ recBoundaries w
      ↔ (⟨i, hi⟩ : Fin (n + 1)) ∈ (rcAsSet w).boundaries := Iff.rfl
  rw [hbdd, CompositionAsSet.mem_boundaries_iff_exists_blocks_sum_take_eq]
  constructor
  · rintro ⟨j, hjlt, hj⟩
    refine ⟨j, ?_, ?_⟩
    · -- j < card boundaries = length + 1
      have hcard := (rcAsSet w).card_boundaries_eq_succ_length
      have : (rcAsSet w).length = (rc w).length :=
        (CompositionAsSet.toComposition_length (rcAsSet w)).symm
      omega
    · -- i = (take j blocks).sum = sizeUpTo j
      have hblocks : (rcAsSet w).blocks = (rc w).blocks :=
        (CompositionAsSet.toComposition_blocks (rcAsSet w)).symm
      have : ((rc w).blocks.take j).sum = (rc w).sizeUpTo j := rfl
      rw [← this, ← hblocks]; exact hj.symm
  · rintro ⟨j, hjle, hj⟩
    refine ⟨j, ?_, ?_⟩
    · have hcard := (rcAsSet w).card_boundaries_eq_succ_length
      have hlen : (rcAsSet w).length = (rc w).length :=
        (CompositionAsSet.toComposition_length (rcAsSet w)).symm
      omega
    · have hblocks : (rcAsSet w).blocks = (rc w).blocks :=
        (CompositionAsSet.toComposition_blocks (rcAsSet w)).symm
      have : ((rc w).blocks.take j).sum = (rc w).sizeUpTo j := rfl
      rw [hblocks, this]; exact hj.symm

/-- **G2 (forward record bookkeeping).**  For a down-up `w` with `rc w = compSnoc m k hk β`,
the global maximum sits at the block-leader position `leaderPos m k`, the head standardization
`disLeft` has record composition `β`, and the block-tail perm is down-up of the right length. -/
lemma rc_compSnoc_forward (m k : ℕ) (hk : k ≤ m) (β : Composition (m - k))
    (w : Equiv.Perm (Fin (2 * (m + 1)))) (hw : IsDownUp w)
    (hrc : rc w = compSnoc m k hk β) :
    posOfMax (by omega) w = leaderPos m k := by
  -- Let q be the position of the global maximum.
  set hm : 1 ≤ 2 * (m + 1) := by omega with hhm
  set q : ℕ := posOfMax hm w with hq
  have hqlt : q < 2 * (m + 1) := posOfMax_lt hm w
  have hwq : (w ⟨q, hqlt⟩ : ℕ) = 2 * (m + 1) - 1 := w_posOfMax hm w
  -- q is even because w is down-up.
  have hpar := (alt_max_pos_parity (2 * (m + 1)) (by omega) w q hqlt hwq).1
    ((isDownUp_iff_isDownUpLen (m + 1) w).1 hw)
  obtain ⟨p, hpeq⟩ := hpar
  -- p := q / 2, so q = 2p and p < m+1.
  have hp2 : q = 2 * p := by omega
  have hplt : p < m + 1 := by omega
  -- hatVal w ⟨p⟩ = w ⟨2p⟩ = w ⟨q⟩ is the global max value.
  have hhat : (hatVal w ⟨p, hplt⟩ : ℕ) = 2 * (m + 1) - 1 := by
    unfold hatVal
    have : (⟨2 * p, by omega⟩ : Fin (2 * (m + 1))) = ⟨q, hqlt⟩ := by
      apply Fin.ext; simp [hp2]
    rw [this]; exact hwq
  -- Because hatVal w p is the maximum value, p is a record.
  have hprec : IsRecord w ⟨p, hplt⟩ := by
    intro j hj
    have hjne : (hatVal w j : ℕ) ≠ (hatVal w ⟨p, hplt⟩ : ℕ) := by
      intro heq
      have : hatVal w j = hatVal w ⟨p, hplt⟩ := Fin.ext heq
      unfold hatVal at this
      have := w.injective this
      have h2 : (2 * (j : ℕ)) = 2 * (p : ℕ) := by
        have := (Fin.mk.injEq _ _ _ _).mp this
        simpa using this
      have hjp : (j : ℕ) < p := hj
      omega
    have hjle : (hatVal w j : ℕ) < 2 * (m + 1) := (hatVal w j).isLt
    rw [Fin.lt_def]
    omega
  -- length and sizeUpTo facts about rc w = compSnoc.
  have hlen : (rc w).length = β.length + 1 := by
    rw [hrc]; exact compSnoc_length m k hk β
  -- sizeUpTo at β.length equals m - k.
  have hsz_mk : (rc w).sizeUpTo β.length = m - k := by
    rw [hrc, compSnoc_sizeUpTo_le m k hk β (le_refl _)]
    have := β.sizeUpTo_length; simpa using this
  -- ============ p ≤ m - k ============
  -- p is a record boundary of w.
  have hp_bdry : (⟨p, by omega⟩ : Fin (m + 1 + 1)) ∈ recBoundaries w := by
    simp only [recBoundaries, Set.mem_toFinset, Set.mem_setOf_eq]
    right
    exact ⟨by simpa using hplt, hprec⟩
  -- via the bridge, p = sizeUpTo j for some j ≤ length.
  have hp_iff := (recBoundaries_mem_iff (m + 1) w p (by omega)).1 hp_bdry
  obtain ⟨j, hjle, hjeq⟩ := hp_iff
  rw [hlen] at hjle
  -- j ≤ β.length (else p = m+1, contradicting p < m+1).
  have hjle' : j ≤ β.length := by
    rcases Nat.lt_or_ge j (β.length + 1) with h | h
    · omega
    · exfalso
      have hj : j = β.length + 1 := by omega
      have : (rc w).sizeUpTo j = m + 1 := by
        rw [hj, hrc, compSnoc_sizeUpTo_last m k hk β]
      omega
  -- p = sizeUpTo j ≤ sizeUpTo β.length = m - k.
  have hp_le : p ≤ m - k := by
    rw [hjeq, ← hsz_mk]
    exact (rc w).monotone_sizeUpTo hjle'
  -- ============ m - k ≤ p ============
  -- m - k is a record boundary of w (via the bridge with j = β.length).
  have hmk_bdry : (⟨m - k, by omega⟩ : Fin (m + 1 + 1)) ∈ recBoundaries w := by
    rw [recBoundaries_mem_iff (m + 1) w (m - k) (by omega)]
    exact ⟨β.length, by rw [hlen]; omega, hsz_mk.symm⟩
  -- unpack: since m - k < m + 1 = n, this gives IsRecord w ⟨m-k⟩.
  have hmk_rec : IsRecord w ⟨m - k, by omega⟩ := by
    simp only [recBoundaries, Set.mem_toFinset, Set.mem_setOf_eq] at hmk_bdry
    rcases hmk_bdry with h | ⟨h, hrec⟩
    · exfalso; omega
    · exact hrec
  -- m - k ≤ p: else p < m-k, and IsRecord at m-k needs hatVal p < hatVal (m-k),
  -- contradicting hatVal p being the global maximum.
  have hmk_ge : m - k ≤ p := by
    by_contra hlt
    push_neg at hlt
    have := hmk_rec ⟨p, by omega⟩ (by simpa using hlt)
    -- hatVal w ⟨p⟩ < hatVal w ⟨m-k⟩ but hatVal w ⟨p⟩ is the max value 2(m+1)-1.
    have hbound : (hatVal w ⟨m - k, by omega⟩ : ℕ) < 2 * (m + 1) := (hatVal w _).isLt
    rw [Fin.lt_def] at this
    -- rewrite hatVal w ⟨p,_⟩ to the max value; the two Fin p mk's agree.
    have hpeq2 : (hatVal w (⟨p, by omega⟩ : Fin (m + 1)) : ℕ)
        = (hatVal w (⟨p, hplt⟩ : Fin (m + 1)) : ℕ) := by rfl
    rw [hpeq2, hhat] at this
    omega
  -- Conclude p = m - k, hence posOfMax = 2p = 2(m-k) = leaderPos.
  have hpk : p = m - k := le_antisymm hp_le hmk_ge
  show q = leaderPos m k
  unfold leaderPos
  omega


/-- The disassembled left segment perm, as a perm of `Fin (2*(m-k))` (note
`leaderPos m k = 2*(m-k)` definitionally, so the cast in `rc_compSnoc_head` is defeq). -/
noncomputable def headPerm (m k : ℕ) (hk : k ≤ m)
    (w : Equiv.Perm (Fin (2 * (m + 1))))
    (hmax : posOfMax (by omega) w = leaderPos m k) :
    Equiv.Perm (Fin (2 * (m - k))) :=
  disLeft (2 * (m + 1)) (leaderPos m k) (by omega) (leaderPos_lt m k hk) w hmax

/-- **H0.** The cast in `rc_compSnoc_head`\'s statement is defeq to `headPerm`. -/
lemma rc_head_cast_eq (m k : ℕ) (hk : k ≤ m)
    (w : Equiv.Perm (Fin (2 * (m + 1))))
    (hmax : posOfMax (by omega) w = leaderPos m k) :
    (show Equiv.Perm (Fin (2 * (m - k))) from
        cast (by rw [leaderPos]) (disLeft (2 * (m + 1)) (leaderPos m k)
          (by omega) (leaderPos_lt m k hk) w hmax))
      = headPerm m k hk w hmax := by
  rfl

/-- **H1 (order transfer).** For positions `a b < 2*(m-k)`, the head perm compares them
the same way `w` compares the corresponding absolute positions. -/
lemma headPerm_lt_iff (m k : ℕ) (hk : k ≤ m)
    (w : Equiv.Perm (Fin (2 * (m + 1))))
    (hmax : posOfMax (by omega) w = leaderPos m k)
    (a b : Fin (2 * (m - k))) :
    headPerm m k hk w hmax a < headPerm m k hk w hmax b
      ↔ (w ⟨(a : ℕ), by have := a.isLt; omega⟩ : Fin (2 * (m + 1)))
          < w ⟨(b : ℕ), by have := b.isLt; omega⟩ := by
  have key := stdSeg_lt_iff (leftVal (2 * (m + 1)) (leaderPos m k) (by omega)
      (leaderPos_lt m k hk) w) (leftVal_injective (by omega) (leaderPos_lt m k hk) w hmax) a b
  refine key.trans ?_
  simp only [leftVal]
  rw [castDown_lt_iff (by omega) (leftPos_val_lt (by omega) (leaderPos_lt m k hk) w hmax _)
    (leftPos_val_lt (by omega) (leaderPos_lt m k hk) w hmax _)]
  have e1 : (leftPos (2 * (m + 1)) (leaderPos m k) (leaderPos_lt m k hk) a : Fin (2 * (m + 1)))
      = ⟨(a : ℕ), by have := a.isLt; omega⟩ := rfl
  have e2 : (leftPos (2 * (m + 1)) (leaderPos m k) (leaderPos_lt m k hk) b : Fin (2 * (m + 1)))
      = ⟨(b : ℕ), by have := b.isLt; omega⟩ := rfl
  rw [e1, e2]

/-- **H2 (records transfer).** For `j < m-k`, the head perm\'s odd-subword record status at
`j` matches `w`\'s record status at `j`. -/
lemma IsRecord_headPerm_iff (m k : ℕ) (hk : k ≤ m)
    (w : Equiv.Perm (Fin (2 * (m + 1)))) (hw : IsDownUp w)
    (hmax : posOfMax (by omega) w = leaderPos m k)
    (j : ℕ) (hj : j < m - k) :
    IsRecord (headPerm m k hk w hmax) ⟨j, hj⟩ ↔ IsRecord w ⟨j, by omega⟩ := by
  unfold IsRecord hatVal
  constructor
  · intro h i hi
    -- i : Fin (m+1+1), i < j.  Set i' : Fin (m-k) := ⟨i, _⟩.
    have hilt : (i : ℕ) < m - k := by
      have : (i : ℕ) < j := hi; omega
    have := h ⟨(i : ℕ), hilt⟩ (by simpa using hi)
    -- this : headPerm ⟨2*i⟩ < headPerm ⟨2*j⟩ ; convert via H1
    have hH := headPerm_lt_iff m k hk w hmax
        ⟨2 * (i : ℕ), by omega⟩ ⟨2 * j, by omega⟩
    -- hH : headPerm ⟨2i⟩ < headPerm ⟨2j⟩ ↔ w ⟨2i⟩ < w ⟨2j⟩
    have hlt := hH.mp this
    simpa using hlt
  · intro h i hi
    -- i : Fin (m-k), i < j.
    have hilt : (i : ℕ) < m + 1 := by omega
    have := h ⟨(i : ℕ), by omega⟩ (by simpa using hi)
    have hH := headPerm_lt_iff m k hk w hmax
        ⟨2 * (i : ℕ), by omega⟩ ⟨2 * j, by omega⟩
    have hlt := hH.mpr (by simpa using this)
    simpa using hlt

/-- **H3 (boundary transfer).** The record boundaries of the head perm are exactly the
record boundaries of `w` that are `≤ m - k`. -/
lemma recBoundaries_headPerm_eq (m k : ℕ) (hk : k ≤ m)
    (w : Equiv.Perm (Fin (2 * (m + 1)))) (hw : IsDownUp w)
    (hmax : posOfMax (by omega) w = leaderPos m k) (i : ℕ) (hi : i < m - k + 1) :
    (⟨i, hi⟩ : Fin (m - k + 1)) ∈ recBoundaries (headPerm m k hk w hmax)
      ↔ (⟨i, by omega⟩ : Fin (m + 1 + 1)) ∈ recBoundaries w := by
  simp only [recBoundaries, Set.mem_toFinset, Set.mem_setOf_eq]
  have hile : i ≤ m - k := by omega
  rcases eq_or_lt_of_le hile with heq | hlt
  · -- i = m - k: LHS terminal-disjunct true; RHS needs IsRecord w ⟨m-k⟩.
    subst heq
    constructor
    · intro _
      right
      refine ⟨by omega, ?_⟩
      -- IsRecord w ⟨m-k⟩ : the max value sits at position 2*(m-k) = leaderPos.
      set hm : 1 ≤ 2 * (m + 1) := by omega with hhm
      have hqlt : posOfMax hm w < 2 * (m + 1) := posOfMax_lt hm w
      have hwq : (w ⟨posOfMax hm w, hqlt⟩ : ℕ) = 2 * (m + 1) - 1 := w_posOfMax hm w
      have hpos : posOfMax hm w = 2 * (m - k) := by
        have := hmax; unfold leaderPos at this; exact this
      have hhat : (hatVal w ⟨m - k, by omega⟩ : ℕ) = 2 * (m + 1) - 1 := by
        unfold hatVal
        have : (⟨2 * (m - k), by omega⟩ : Fin (2 * (m + 1)))
            = ⟨posOfMax hm w, hqlt⟩ := by apply Fin.ext; simp [hpos]
        rw [this]; exact hwq
      intro j hj
      have hjne : (hatVal w j : ℕ) ≠ (hatVal w ⟨m - k, by omega⟩ : ℕ) := by
        intro heq2
        have : hatVal w j = hatVal w ⟨m - k, by omega⟩ := Fin.ext heq2
        unfold hatVal at this
        have := w.injective this
        have h2 : (2 * (j : ℕ)) = 2 * (m - k) := by
          have := (Fin.mk.injEq _ _ _ _).mp this
          simpa using this
        have hjp : (j : ℕ) < m - k := hj
        omega
      have hjle : (hatVal w j : ℕ) < 2 * (m + 1) := (hatVal w j).isLt
      rw [Fin.lt_def]; omega
    · intro _; left; rfl
  · -- i < m - k: both terminal disjuncts false; reduce to IsRecord equiv via H2.
    constructor
    · rintro (h | ⟨h, hrec⟩)
      · exfalso; omega
      · right
        refine ⟨by omega, ?_⟩
        exact (IsRecord_headPerm_iff m k hk w hw hmax i hlt).mp hrec
    · rintro (h | ⟨h, hrec⟩)
      · exfalso; omega
      · right
        refine ⟨hlt, ?_⟩
        exact (IsRecord_headPerm_iff m k hk w hw hmax i hlt).mpr hrec

/-- Round-trip: `toCompositionAsSet` then `toComposition` is the identity. -/
lemma toCompositionAsSet_toComposition {p : ℕ} (x : Composition p) :
    x.toCompositionAsSet.toComposition = x := by
  apply Composition.ext
  rw [CompositionAsSet.toComposition_blocks, Composition.toCompositionAsSet_blocks]

/-- Membership in `Composition.boundaries` as a partial-sum condition. -/
lemma Composition.mem_boundaries_iff_sizeUpTo {p : ℕ} (x : Composition p) (i : ℕ)
    (hi : i < p + 1) :
    (⟨i, hi⟩ : Fin (p + 1)) ∈ x.boundaries
      ↔ ∃ j, j ≤ x.length ∧ i = x.sizeUpTo j := by
  rw [← x.toCompositionAsSet_boundaries,
    CompositionAsSet.mem_boundaries_iff_exists_blocks_sum_take_eq]
  constructor
  · rintro ⟨j, hj1, hj2⟩
    refine ⟨j, ?_, ?_⟩
    · have hcard := x.toCompositionAsSet.card_boundaries_eq_succ_length
      have hlen : x.toCompositionAsSet.length = x.length := Composition.toCompositionAsSet_length x
      omega
    · have hb : x.toCompositionAsSet.blocks = x.blocks := Composition.toCompositionAsSet_blocks x
      have hsz : (x.blocks.take j).sum = x.sizeUpTo j := rfl
      rw [hb] at hj2; rw [← hsz]; exact hj2.symm
  · rintro ⟨j, hj1, hj2⟩
    refine ⟨j, ?_, ?_⟩
    · have hcard := x.toCompositionAsSet.card_boundaries_eq_succ_length
      have hlen : x.toCompositionAsSet.length = x.length := Composition.toCompositionAsSet_length x
      omega
    · have hb : x.toCompositionAsSet.blocks = x.blocks := Composition.toCompositionAsSet_blocks x
      have hsz : (x.blocks.take j).sum = x.sizeUpTo j := rfl
      rw [hb, hsz]; exact hj2.symm

/-- Reduce the `compSnoc` partial-sum existential (for `i ≤ m - k`) to one over `β`. -/
lemma compSnoc_sizeUpTo_reduce (m k : ℕ) (hk : k ≤ m) (β : Composition (m - k))
    (i : ℕ) (hile : i ≤ m - k) :
    (∃ j, j ≤ (compSnoc m k hk β).length ∧ i = (compSnoc m k hk β).sizeUpTo j)
      ↔ (∃ j, j ≤ β.length ∧ i = β.sizeUpTo j) := by
  rw [compSnoc_length]
  constructor
  · rintro ⟨j, hj1, hj2⟩
    rcases Nat.lt_or_ge j (β.length + 1) with h | h
    · refine ⟨j, by omega, ?_⟩
      rw [compSnoc_sizeUpTo_le m k hk β (by omega)] at hj2; exact hj2
    · have hj : j = β.length + 1 := by omega
      rw [hj, compSnoc_sizeUpTo_last m k hk β] at hj2
      omega
  · rintro ⟨j, hj1, hj2⟩
    refine ⟨j, by omega, ?_⟩
    rw [compSnoc_sizeUpTo_le m k hk β hj1]; exact hj2

/-- **G2b.**  Under the same hypotheses, the head standardization has record composition `β`.
`disLeft` is a perm of `Fin (2*(m-k))`; via `rc` it is a `Composition (m-k)`. -/
lemma rc_compSnoc_head (m k : ℕ) (hk : k ≤ m) (β : Composition (m - k))
    (w : Equiv.Perm (Fin (2 * (m + 1)))) (hw : IsDownUp w)
    (hrc : rc w = compSnoc m k hk β)
    (hmax : posOfMax (by omega) w = leaderPos m k) :
    rc (show Equiv.Perm (Fin (2 * (m - k))) from
        cast (by rw [leaderPos]) (disLeft (2 * (m + 1)) (leaderPos m k)
          (by omega) (leaderPos_lt m k hk) w hmax)) = β := by
  rw [rc_head_cast_eq m k hk w hmax]
  have hbdd : rcAsSet (headPerm m k hk w hmax) = β.toCompositionAsSet := by
    apply CompositionAsSet.ext
    show recBoundaries (headPerm m k hk w hmax) = β.toCompositionAsSet.boundaries
    rw [Composition.toCompositionAsSet_boundaries]
    ext ⟨i, hi⟩
    rw [recBoundaries_headPerm_eq m k hk w hw hmax i hi,
      recBoundaries_mem_iff (m + 1) w i (by omega), hrc,
      compSnoc_sizeUpTo_reduce m k hk β i (by omega),
      Composition.mem_boundaries_iff_sizeUpTo β i hi]
  show (rcAsSet (headPerm m k hk w hmax)).toComposition = β
  rw [hbdd, toCompositionAsSet_toComposition]

/-! ### The four `card_bij'` obligations for `N_compSnoc`.

We instantiate the generic machinery at `m' := 2*(m+1)`, `k' := leaderPos m k = 2*(m-k)`.
Sizes:  `m'-1 = 2*(m+1)-1`,  head length `k' = 2*(m-k)`,  block-tail length
`m'-1-k' = 2*(k+1)-1`.  The forward map sends a fiber element `w` to the triple
`((leftValSet …)ᶜ , blockTailPerm … , headPerm …)`; the inverse assembles
`assemblePerm m' k' Sᶜ … ℓ (r.trans Fin.revPerm)`. -/

/-- Block-tail length identity:  `2*(m+1)-1 - leaderPos m k = 2*(k+1)-1`. -/
lemma blockTail_size_eq (m k : ℕ) (hk : k ≤ m) :
    2 * (m + 1) - 1 - leaderPos m k = 2 * (k + 1) - 1 := by
  unfold leaderPos; omega

/-- Cast a block-tail perm to the `blockSplitData` `r`-slot type. -/
noncomputable def btCast (m k : ℕ) (hk : k ≤ m)
    (p : Equiv.Perm (Fin (2 * (m + 1) - 1 - leaderPos m k))) :
    Equiv.Perm (Fin (2 * (k + 1) - 1)) :=
  (finCongr (blockTail_size_eq m k hk)).permCongr p

/-- Cast a `blockSplitData` `r`-slot perm back to the block-tail type. -/
noncomputable def btCastInv (m k : ℕ) (hk : k ≤ m)
    (p : Equiv.Perm (Fin (2 * (k + 1) - 1))) :
    Equiv.Perm (Fin (2 * (m + 1) - 1 - leaderPos m k)) :=
  (finCongr (blockTail_size_eq m k hk)).symm.permCongr p

lemma btCast_btCastInv (m k : ℕ) (hk : k ≤ m)
    (p : Equiv.Perm (Fin (2 * (k + 1) - 1))) :
    btCast m k hk (btCastInv m k hk p) = p := by
  unfold btCast btCastInv
  ext x
  simp [Equiv.permCongr_apply, finCongr_symm]

lemma btCastInv_btCast (m k : ℕ) (hk : k ≤ m)
    (p : Equiv.Perm (Fin (2 * (m + 1) - 1 - leaderPos m k))) :
    btCastInv m k hk (btCast m k hk p) = p := by
  unfold btCast btCastInv
  ext x
  simp [Equiv.permCongr_apply, finCongr_symm]

/-- The round-trip `btCastInv (btCast p ∘ rev) = p ∘ rev`: reversing commutes with the
size-cast `finCongr`, since both `Fin.rev`s are on equal-sized `Fin`s. -/
lemma btCastInv_btCast_trans_revPerm (m k : ℕ) (hk : k ≤ m)
    (p : Equiv.Perm (Fin (2 * (m + 1) - 1 - leaderPos m k))) :
    btCastInv m k hk ((btCast m k hk p).trans Fin.revPerm)
      = p.trans Fin.revPerm := by
  unfold btCast btCastInv
  ext x
  simp only [Equiv.permCongr_apply, Equiv.trans_apply, finCongr_symm, finCongr_apply,
    Fin.revPerm_apply, Fin.cast_cast, Fin.cast_eq_self]
  simp only [Fin.val_rev, Fin.val_cast]
  have hsz := blockTail_size_eq m k hk
  omega

/-- The round-trip `btCast (btCastInv p ∘ rev) = p ∘ rev`, the mirror of
`btCastInv_btCast_trans_revPerm`. -/
lemma btCast_btCastInv_trans_revPerm (m k : ℕ) (hk : k ≤ m)
    (p : Equiv.Perm (Fin (2 * (k + 1) - 1))) :
    btCast m k hk ((btCastInv m k hk p).trans Fin.revPerm)
      = p.trans Fin.revPerm := by
  unfold btCast btCastInv
  ext x
  simp only [Equiv.permCongr_apply, Equiv.trans_apply, finCongr_symm, finCongr_apply,
    Fin.revPerm_apply, Fin.cast_cast, Fin.cast_eq_self]
  simp only [Fin.val_rev, Fin.val_cast]
  have hsz := blockTail_size_eq m k hk
  omega

/-- `IsUpDownLen` is preserved by the size-cast `(finCongr h).permCongr`. -/
lemma IsUpDownLen_finCongr_permCongr {a b : ℕ} (h : a = b)
    (p : Equiv.Perm (Fin a)) (hp : IsUpDownLen a p) :
    IsUpDownLen b ((finCongr h).permCongr p) := by
  subst h
  intro j hj
  have hpj := hp j hj
  simp only [Equiv.permCongr_apply, finCongr_symm, finCongr_apply, Fin.cast_eq_self]
  simpa using hpj

/-- The `r`-slot of `blockSplitData`, after `∘ rev` and the size-cast `btCastInv`,
lands in `upDownPermsLen` of the block-tail size. -/
lemma btCastInv_trans_revPerm_mem_upDown (m k : ℕ) (hk : k ≤ m)
    (r : Equiv.Perm (Fin (2 * (k + 1) - 1)))
    (hr : r ∈ downUpPermsLen (2 * (k + 1) - 1)) :
    btCastInv m k hk (r.trans Fin.revPerm)
      ∈ upDownPermsLen (2 * (m + 1) - 1 - leaderPos m k) := by
  -- r.trans revPerm is up-down
  have hru : IsUpDownLen (2 * (k + 1) - 1) (r.trans Fin.revPerm) := by
    simp only [downUpPermsLen, Set.mem_toFinset, Set.mem_setOf_eq] at hr
    intro j h
    have hrj := hr j h
    simp only [Equiv.trans_apply, Fin.revPerm_apply]
    split_ifs at hrj ⊢ with hj
    · exact Fin.rev_lt_rev.mpr hrj
    · exact Fin.rev_lt_rev.mpr hrj
  simp only [upDownPermsLen, Set.mem_toFinset, Set.mem_setOf_eq]
  unfold btCastInv
  rw [finCongr_symm]
  exact IsUpDownLen_finCongr_permCongr (blockTail_size_eq m k hk).symm _ hru

/-- `IsDownUpLen` is preserved by the size-cast `(finCongr h).permCongr`. -/
lemma IsDownUpLen_finCongr_permCongr {a b : ℕ} (h : a = b)
    (p : Equiv.Perm (Fin a)) (hp : IsDownUpLen a p) :
    IsDownUpLen b ((finCongr h).permCongr p) := by
  subst h
  intro j hj
  have hpj := hp j hj
  simp only [Equiv.permCongr_apply, finCongr_symm, finCongr_apply, Fin.cast_eq_self]
  simpa using hpj

/-- The block-tail slot: an up-down `disRight`, reversed and size-cast, is down-up of the
`r`-slot length `2*(k+1)-1`. -/
lemma btCast_trans_revPerm_mem_downUp (m k : ℕ) (hk : k ≤ m)
    (p : Equiv.Perm (Fin (2 * (m + 1) - 1 - leaderPos m k)))
    (hp : p ∈ upDownPermsLen (2 * (m + 1) - 1 - leaderPos m k)) :
    btCast m k hk (p.trans Fin.revPerm) ∈ downUpPermsLen (2 * (k + 1) - 1) := by
  -- p.trans revPerm is down-up
  have hpd : IsDownUpLen (2 * (m + 1) - 1 - leaderPos m k) (p.trans Fin.revPerm) := by
    simp only [upDownPermsLen, Set.mem_toFinset, Set.mem_setOf_eq] at hp
    intro j h
    have hpj := hp j h
    simp only [Equiv.trans_apply, Fin.revPerm_apply]
    split_ifs at hpj ⊢ with hj
    · exact Fin.rev_lt_rev.mpr hpj
    · exact Fin.rev_lt_rev.mpr hpj
  simp only [downUpPermsLen, Set.mem_toFinset, Set.mem_setOf_eq]
  unfold btCast
  exact IsDownUpLen_finCongr_permCongr (blockTail_size_eq m k hk) _ hpd

/-- Forward map lands in `blockSplitData`. -/
lemma Ncs_fwd_mem (m k : ℕ) (hk : k ≤ m) (β : Composition (m - k))
    (w : Equiv.Perm (Fin (2 * (m + 1))))
    (hw : w ∈ downUpPerms (m + 1)) (hrc : rc w = compSnoc m k hk β) :
    haveI hwdu : IsDownUp w := by
      have := hw; rw [downUpPerms] at this
      simpa only [Set.mem_toFinset, Set.mem_setOf_eq] using this
    haveI hmax : posOfMax (by omega) w = leaderPos m k :=
      rc_compSnoc_forward m k hk β w hwdu hrc
    ((leftValSet (2 * (m + 1)) (leaderPos m k) (by omega) (leaderPos_lt m k hk) w)ᶜ,
      btCast m k hk (blockTailPerm m k hk w hmax), headPerm m k hk w hmax)
      ∈ blockSplitData m k hk β := by
  haveI hwdu : IsDownUp w := by
    have := hw; rw [downUpPerms] at this
    simpa only [Set.mem_toFinset, Set.mem_setOf_eq] using this
  haveI hmax : posOfMax (by omega) w = leaderPos m k :=
    rc_compSnoc_forward m k hk β w hwdu hrc
  -- `w ∈ altPermsLen` (it is down-up)
  have hwalt : w ∈ altPermsLen (2 * (m + 1)) := by
    rw [altPermsLen, Finset.mem_union]
    left
    simp only [downUpPermsLen, Set.mem_toFinset, Set.mem_setOf_eq]
    exact (isDownUp_iff_isDownUpLen (m + 1) w).1 hwdu
  -- generic disassembly membership
  have hgen := disassemble_mem_splitData (m := 2 * (m + 1)) (k := leaderPos m k)
    (by omega) (leaderPos_lt m k hk) w hwalt hmax
  rw [splitData, Finset.mem_product, Finset.mem_product] at hgen
  obtain ⟨hgS, hgℓ, hgr⟩ := hgen
  -- unfold membership of the goal in `blockSplitData`
  rw [blockSplitData, Finset.mem_product, Finset.mem_product]
  refine ⟨?_, ?_, ?_⟩
  · -- (leftValSet w)ᶜ ∈ powersetCard (2*(k+1)-1)
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_compl, Fintype.card_fin,
      leftValSet_card (by omega) (leaderPos_lt m k hk) w hmax]
    unfold leaderPos; omega
  · -- btCast (blockTailPerm w) ∈ downUpPermsLen (2*(k+1)-1)
    unfold blockTailPerm
    exact btCast_trans_revPerm_mem_downUp m k hk _ hgr
  · -- headPerm w ∈ filter (rc = β) (downUpPerms (m-k))
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · -- headPerm w ∈ downUpPerms (m-k)
      rw [downUpPerms_eq_downUpPermsLen]
      -- headPerm = disLeft ∈ leftAltPerms leaderPos = downUpPermsLen leaderPos
      have hev : Even (leaderPos m k) := ⟨m - k, by unfold leaderPos; ring⟩
      rw [leftAltPerms, if_pos hev] at hgℓ
      -- disLeft w ∈ downUpPermsLen leaderPos, and headPerm = disLeft, leaderPos = 2*(m-k) defeq
      show headPerm m k hk w hmax ∈ downUpPermsLen (2 * (m - k))
      unfold headPerm
      exact hgℓ
    · -- rc (headPerm w) = β
      have := rc_compSnoc_head m k hk β w hwdu hrc hmax
      rwa [rc_head_cast_eq m k hk w hmax] at this

/-- `disassemble ∘ assemble = id` on `blockSplitData` (block side).
Stated with the assembled permutation `W`, its down-up witness `hwdu`, and its
max-position identity `hmax` supplied as explicit arguments, so that the type does not
force any expensive reduction of `assemblePerm` at elaboration time. -/
lemma Ncs_right_inv (m k : ℕ) (hk : k ≤ m) (β : Composition (m - k))
    (S : Finset (Fin (2 * (m + 1) - 1)))
    (r : Equiv.Perm (Fin (2 * (k + 1) - 1)))
    (ℓ : Equiv.Perm (Fin (2 * (m - k))))
    (hd : (S, r, ℓ) ∈ blockSplitData m k hk β)
    (hSc : Sᶜ.card = leaderPos m k)
    (W : Equiv.Perm (Fin (2 * (m + 1))))
    (hWeq : W = assemblePerm (2 * (m + 1)) (leaderPos m k) (by omega) (leaderPos_lt m k hk)
        Sᶜ hSc ℓ (btCastInv m k hk (r.trans Fin.revPerm)))
    (hwdu : IsDownUp W)
    (hmax : posOfMax (by omega) W = leaderPos m k) :
    ((leftValSet (2 * (m + 1)) (leaderPos m k) (by omega) (leaderPos_lt m k hk) W)ᶜ,
      btCast m k hk (blockTailPerm m k hk W hmax), headPerm m k hk W hmax) = (S, r, ℓ) := by
  -- membership facts extracted from `hd`
  obtain ⟨hdS, hd2⟩ := Finset.mem_product.mp hd
  obtain ⟨hdr, hdℓ⟩ := Finset.mem_product.mp hd2
  -- ℓ ∈ leftAltPerms (leaderPos m k):  leaderPos is even, so leftAltPerms = downUpPermsLen
  have hℓ : ℓ ∈ leftAltPerms (leaderPos m k) := by
    have hev : Even (leaderPos m k) := ⟨m - k, by unfold leaderPos; ring⟩
    unfold leftAltPerms
    rw [if_pos hev]
    -- ℓ ∈ downUpPerms (m-k) = downUpPermsLen (2*(m-k)) = downUpPermsLen (leaderPos m k)
    have hℓ' : ℓ ∈ downUpPerms (m - k) := (Finset.mem_filter.mp hdℓ).1
    rw [downUpPerms_eq_downUpPermsLen] at hℓ'
    show ℓ ∈ downUpPermsLen (leaderPos m k)
    unfold leaderPos; exact hℓ'
  -- r-slot membership after cast + reversal
  have hr : btCastInv m k hk (r.trans Fin.revPerm)
      ∈ upDownPermsLen (2 * (m + 1) - 1 - leaderPos m k) :=
    btCastInv_trans_revPerm_mem_upDown m k hk r
      (Finset.mem_product.mp hd2).1
  -- disassemble ∘ assemble = id via the generic lemma
  have key := disassemble_assemble (m := 2 * (m + 1)) (k := leaderPos m k)
    (by omega) (leaderPos_lt m k hk) Sᶜ hSc ℓ
    (btCastInv m k hk (r.trans Fin.revPerm)) hℓ hr
  -- rewrite W by its definition
  subst hWeq
  -- the generic hmax used in `key`; ours is proof-irrelevant equal
  set hmax' := posOfMax_assemblePerm (2 * (m + 1)) (leaderPos m k) (by omega)
    (leaderPos_lt m k hk) Sᶜ hSc ℓ (btCastInv m k hk (r.trans Fin.revPerm)) with hmax'def
  rw [Prod.mk.injEq, Prod.mk.injEq] at key
  obtain ⟨hkey1, hkey2, hkey3⟩ := key
  -- our `hmax` equals the generic one by proof irrelevance
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · -- component 1: (leftValSet W)ᶜ = S
    show (leftValSet (2 * (m + 1)) (leaderPos m k) (by omega) (leaderPos_lt m k hk) _)ᶜ = S
    rw [hkey1, compl_compl]
  · -- component 2: btCast (blockTailPerm W hmax) = r
    show btCast m k hk (blockTailPerm m k hk _ hmax) = r
    unfold blockTailPerm
    rw [show (disRight (2 * (m + 1)) (leaderPos m k) (by omega) (leaderPos_lt m k hk) _ hmax)
          = disRight (2 * (m + 1)) (leaderPos m k) (by omega) (leaderPos_lt m k hk) _ hmax'
        from by congr 1,
      hkey3, btCast_btCastInv_trans_revPerm, Equiv.trans_assoc,
      show (Fin.revPerm.trans Fin.revPerm : Equiv.Perm (Fin (2 * (k + 1) - 1)))
          = Equiv.refl _ from by ext y; simp [Fin.rev_rev],
      Equiv.trans_refl]
  · -- component 3: headPerm W hmax = ℓ
    show headPerm m k hk _ hmax = ℓ
    unfold headPerm
    rw [show (disLeft (2 * (m + 1)) (leaderPos m k) (by omega) (leaderPos_lt m k hk) _ hmax)
          = disLeft (2 * (m + 1)) (leaderPos m k) (by omega) (leaderPos_lt m k hk) _ hmax'
        from by congr 1,
      hkey2]

/-- Inverse map lands in the fiber `{w ∈ downUpPerms (m+1) | rc w = compSnoc m k hk β}`. -/
lemma Ncs_inv_mem (m k : ℕ) (hk : k ≤ m) (β : Composition (m - k))
    (S : Finset (Fin (2 * (m + 1) - 1)))
    (r : Equiv.Perm (Fin (2 * (k + 1) - 1)))
    (ℓ : Equiv.Perm (Fin (2 * (m - k))))
    (hd : (S, r, ℓ) ∈ blockSplitData m k hk β)
    (hSc : Sᶜ.card = leaderPos m k) :
    haveI W : Equiv.Perm (Fin (2 * (m + 1))) :=
      assemblePerm (2 * (m + 1)) (leaderPos m k) (by omega) (leaderPos_lt m k hk)
        Sᶜ hSc ℓ (btCastInv m k hk (r.trans Fin.revPerm))
    W ∈ downUpPerms (m + 1) ∧ rc W = compSnoc m k hk β := by
  -- Abbreviations
  set W : Equiv.Perm (Fin (2 * (m + 1))) :=
    assemblePerm (2 * (m + 1)) (leaderPos m k) (by omega) (leaderPos_lt m k hk)
      Sᶜ hSc ℓ (btCastInv m k hk (r.trans Fin.revPerm)) with hWdef
  -- Extract membership facts from `hd` (mirrors `Ncs_right_inv`).
  obtain ⟨hdS, hd2⟩ := Finset.mem_product.mp hd
  obtain ⟨hdr, hdℓ⟩ := Finset.mem_product.mp hd2
  -- ℓ ∈ leftAltPerms (leaderPos m k) : leaderPos even ⟹ leftAltPerms = downUpPermsLen.
  have hev : Even (leaderPos m k) := ⟨m - k, by unfold leaderPos; ring⟩
  have hℓ : ℓ ∈ leftAltPerms (leaderPos m k) := by
    unfold leftAltPerms
    rw [if_pos hev]
    have hℓ' : ℓ ∈ downUpPerms (m - k) := (Finset.mem_filter.mp hdℓ).1
    rw [downUpPerms_eq_downUpPermsLen] at hℓ'
    show ℓ ∈ downUpPermsLen (leaderPos m k)
    unfold leaderPos; exact hℓ'
  have hr : btCastInv m k hk (r.trans Fin.revPerm)
      ∈ upDownPermsLen (2 * (m + 1) - 1 - leaderPos m k) :=
    btCastInv_trans_revPerm_mem_upDown m k hk r (Finset.mem_product.mp hd2).1
  -- `posOfMax W = leaderPos m k` (generic).
  have hmaxW : posOfMax (by omega) W = leaderPos m k := by
    rw [hWdef]
    exact posOfMax_assemblePerm (2 * (m + 1)) (leaderPos m k) (by omega)
      (leaderPos_lt m k hk) Sᶜ hSc ℓ (btCastInv m k hk (r.trans Fin.revPerm))
  -- `rc ℓ = β` from the filter component of `hd`.
  have hrcℓ : rc ℓ = β := (Finset.mem_filter.mp hdℓ).2
  -- === Part 1 : W is down-up. ===
  have hWdu : IsDownUp W := by
    have hWalt : W ∈ altPermsLen (2 * (m + 1)) := by
      rw [hWdef]
      exact assemblePerm_mem_fiber (by omega) (leaderPos_lt m k hk) Sᶜ hSc ℓ
        (btCastInv m k hk (r.trans Fin.revPerm)) hℓ hr
    rw [altPermsLen, Finset.mem_union] at hWalt
    rcases hWalt with hdu | hud
    · exact (isDownUp_iff_isDownUpLen (m + 1) W).2
        ((by simpa only [downUpPermsLen, Set.mem_toFinset, Set.mem_setOf_eq] using hdu :
          IsDownUpLen (2 * (m + 1)) W))
    · exfalso
      have hudlen : IsUpDownLen (2 * (m + 1)) W := by
        simpa only [upDownPermsLen, Set.mem_toFinset, Set.mem_setOf_eq] using hud
      have hqlt : posOfMax (by omega : 1 ≤ 2 * (m + 1)) W < 2 * (m + 1) :=
        posOfMax_lt (by omega) W
      have hwq : (W ⟨posOfMax (by omega : 1 ≤ 2 * (m + 1)) W, hqlt⟩ : ℕ) = 2 * (m + 1) - 1 :=
        w_posOfMax (by omega) W
      have hpar := (alt_max_pos_parity (2 * (m + 1)) (by omega) W
        (posOfMax (by omega : 1 ≤ 2 * (m + 1)) W) hqlt hwq).2 hudlen
      apply hpar
      rw [hmaxW]; exact hev
  -- === Part 2 ===
  refine ⟨?_, ?_⟩
  · rw [downUpPerms]
    simpa only [Set.mem_toFinset, Set.mem_setOf_eq] using hWdu
  · -- headPerm W hmaxW = ℓ, via disassemble_assemble (component 3).
    have hℓeq : headPerm m k hk W hmaxW = ℓ := by
      have htriple := Ncs_right_inv m k hk β S r ℓ hd hSc W hWdef hWdu hmaxW
      rw [Prod.mk.injEq, Prod.mk.injEq] at htriple
      exact htriple.2.2
    have hrchead : rc (headPerm m k hk W hmaxW) = β := by rw [hℓeq]; exact hrcℓ
    show (rcAsSet W).toComposition = compSnoc m k hk β
    have hbdd : rcAsSet W = (compSnoc m k hk β).toCompositionAsSet := by
      apply CompositionAsSet.ext
      show recBoundaries W = (compSnoc m k hk β).toCompositionAsSet.boundaries
      rw [Composition.toCompositionAsSet_boundaries]
      ext ⟨i, hi⟩
      rcases Nat.lt_or_ge i (m - k + 1) with hilt | hige
      · have hile : i ≤ m - k := by omega
        rw [← recBoundaries_headPerm_eq m k hk W hWdu hmaxW i hilt,
          recBoundaries_mem_iff (m - k) (headPerm m k hk W hmaxW) i hilt,
          hrchead,
          ← compSnoc_sizeUpTo_reduce m k hk β i hile,
          ← Composition.mem_boundaries_iff_sizeUpTo (compSnoc m k hk β) i hi]
      · rcases Nat.lt_or_ge i (m + 1) with himid | hilast
        · have hnotL : (⟨i, hi⟩ : Fin (m + 1 + 1)) ∉ recBoundaries W := by
            simp only [recBoundaries, Set.mem_toFinset, Set.mem_setOf_eq, not_or,
              not_exists]
            refine ⟨by omega, ?_⟩
            intro hlt hrec
            have hqlt : posOfMax (by omega : 1 ≤ 2 * (m + 1)) W < 2 * (m + 1) :=
              posOfMax_lt (by omega) W
            have hwq : (W ⟨posOfMax (by omega : 1 ≤ 2 * (m + 1)) W, hqlt⟩ : ℕ)
                = 2 * (m + 1) - 1 := w_posOfMax (by omega) W
            have hpos : posOfMax (by omega : 1 ≤ 2 * (m + 1)) W = 2 * (m - k) := by
              have := hmaxW; unfold leaderPos at this; exact this
            have hhat : (hatVal W ⟨m - k, by omega⟩ : ℕ) = 2 * (m + 1) - 1 := by
              unfold hatVal
              have hidx : (⟨2 * (m - k), by omega⟩ : Fin (2 * (m + 1)))
                  = ⟨posOfMax (by omega : 1 ≤ 2 * (m + 1)) W, hqlt⟩ := by
                apply Fin.ext; simp [hpos]
              rw [hidx]; exact hwq
            have hmklt : (m - k : ℕ) < i := by omega
            have hlt2 := hrec ⟨m - k, by omega⟩ (by simpa using hmklt)
            have hle : (hatVal W ⟨i, hlt⟩ : ℕ) < 2 * (m + 1) := (hatVal W ⟨i, hlt⟩).isLt
            rw [Fin.lt_def, hhat] at hlt2
            omega
          have hnotR : (⟨i, hi⟩ : Fin (m + 1 + 1)) ∉ (compSnoc m k hk β).boundaries := by
            rw [Composition.mem_boundaries_iff_sizeUpTo (compSnoc m k hk β) i hi]
            rintro ⟨j, hjle, hjeq⟩
            rw [compSnoc_length] at hjle
            rcases Nat.lt_or_ge j (β.length + 1) with hjlt | hjge
            · rw [compSnoc_sizeUpTo_le m k hk β (by omega)] at hjeq
              have hbound : β.sizeUpTo j ≤ m - k := by
                have h1 : β.sizeUpTo j ≤ β.sizeUpTo β.length :=
                  β.monotone_sizeUpTo (by omega)
                rw [β.sizeUpTo_length] at h1; exact h1
              omega
            · have hj : j = β.length + 1 := by omega
              rw [hj, compSnoc_sizeUpTo_last m k hk β] at hjeq
              omega
          simp only [hnotL, hnotR]
        · have hieq : i = m + 1 := by omega
          have hL : (⟨i, hi⟩ : Fin (m + 1 + 1)) ∈ recBoundaries W := by
            simp only [recBoundaries, Set.mem_toFinset, Set.mem_setOf_eq]
            left; simpa using hieq
          have hR : (⟨i, hi⟩ : Fin (m + 1 + 1)) ∈ (compSnoc m k hk β).boundaries := by
            rw [Composition.mem_boundaries_iff_sizeUpTo (compSnoc m k hk β) i hi]
            refine ⟨β.length + 1, by rw [compSnoc_length], ?_⟩
            rw [compSnoc_sizeUpTo_last m k hk β]; exact hieq
          simp only [hL, hR]
    rw [hbdd, toCompositionAsSet_toComposition]

/-- `assemble ∘ disassemble = id` on the fiber (block side). -/
lemma Ncs_left_inv (m k : ℕ) (hk : k ≤ m) (β : Composition (m - k))
    (w : Equiv.Perm (Fin (2 * (m + 1))))
    (hw : w ∈ downUpPerms (m + 1)) (hrc : rc w = compSnoc m k hk β) :
    haveI hwdu : IsDownUp w := by
      have := hw; rw [downUpPerms] at this
      simpa only [Set.mem_toFinset, Set.mem_setOf_eq] using this
    haveI hmax : posOfMax (by omega) w = leaderPos m k :=
      rc_compSnoc_forward m k hk β w hwdu hrc
    assemblePerm (2 * (m + 1)) (leaderPos m k) (by omega) (leaderPos_lt m k hk)
        (leftValSet (2 * (m + 1)) (leaderPos m k) (by omega) (leaderPos_lt m k hk) w)ᶜᶜ
        (by rw [compl_compl,
              leftValSet_card (by omega) (leaderPos_lt m k hk) w hmax])
        (headPerm m k hk w hmax)
        (btCastInv m k hk ((btCast m k hk (blockTailPerm m k hk w hmax)).trans Fin.revPerm)) = w := by
  have hwdu : IsDownUp w := by
    have := hw; rw [downUpPerms] at this
    simpa only [Set.mem_toFinset, Set.mem_setOf_eq] using this
  have hmax : posOfMax (by omega) w = leaderPos m k :=
    rc_compSnoc_forward m k hk β w hwdu hrc
  have hwalt : w ∈ altPermsLen (2 * (m + 1)) := by
    rw [altPermsLen]
    apply Finset.mem_union_left
    rw [← downUpPerms_eq_downUpPermsLen]; exact hw
  have key := assemble_disassemble (m := 2 * (m + 1)) (k := leaderPos m k)
    (by omega) (leaderPos_lt m k hk) w hwalt hmax
  rw [btCastInv_btCast_trans_revPerm]
  unfold blockTailPerm headPerm
  rw [Equiv.trans_assoc,
    show (Fin.revPerm.trans Fin.revPerm : Equiv.Perm (Fin (2 * (m + 1) - 1 - leaderPos m k)))
        = Equiv.refl _ from by ext y; simp [Fin.rev_rev],
    Equiv.trans_refl]
  simp only [compl_compl]
  exact key


set_option maxHeartbeats 400000 in
/-- **Block recursion for `N` (last-block peel), the bijective kernel.**

The full bijection between `{w ∈ downUpPerms (m+1) | rc w = compSnoc m k hk β}` and
`blockSplitData m k hk β`, reusing the generic split machinery at `m' = 2(m+1)`,
`k' = leaderPos m k = 2(m-k)`.  The remaining content (record bookkeeping + parity/reversal
conversion of the block tail) is packaged into the lemmas above and the
`card_bij'` obligations below. -/
lemma N_compSnoc (m k : ℕ) (hk : k ≤ m) (β : Composition (m - k)) :
    N (compSnoc m k hk β)
      = Nat.choose (2 * (m + 1) - 1) (2 * (k + 1) - 1)
          * euler (2 * (k + 1) - 1) * N β := by
  rw [← blockSplitData_card m k hk β]
  unfold N
  -- Bijection via card_bij' at m' = 2(m+1), k' = leaderPos m k.
  apply Finset.card_bij'
    (i := fun (w : Equiv.Perm (Fin (2 * (m + 1)))) hw =>
      haveI hwdu : IsDownUp w := by
        have := (Finset.mem_filter.mp hw).1; rw [downUpPerms] at this
        simpa only [Set.mem_toFinset, Set.mem_setOf_eq] using this
      haveI hmax : posOfMax (m := 2 * (m + 1)) (by omega) w = leaderPos m k :=
        rc_compSnoc_forward m k hk β w hwdu (Finset.mem_filter.mp hw).2
      ((leftValSet (2 * (m + 1)) (leaderPos m k) (by omega) (leaderPos_lt m k hk) w)ᶜ,
        btCast m k hk (blockTailPerm m k hk w hmax), headPerm m k hk w hmax))
    (j := fun d hd =>
      assemblePerm (2 * (m + 1)) (leaderPos m k) (by omega) (leaderPos_lt m k hk)
        d.1ᶜ
        (by
          have hcard : d.1.card = 2 * (k + 1) - 1 :=
            (Finset.mem_powersetCard.mp (Finset.mem_product.mp hd).1).2
          rw [Finset.card_compl, Fintype.card_fin, hcard]; unfold leaderPos; omega)
        d.2.2 (btCastInv m k hk (d.2.1.trans Fin.revPerm)))
  case hi =>
    intro w hw
    exact Ncs_fwd_mem m k hk β w (Finset.mem_filter.mp hw).1 (Finset.mem_filter.mp hw).2
  case hj =>
    intro d hd
    rw [Finset.mem_filter]
    exact Ncs_inv_mem m k hk β d.1 d.2.1 d.2.2 hd _
  case left_inv =>
    intro w hw
    exact Ncs_left_inv m k hk β w (Finset.mem_filter.mp hw).1 (Finset.mem_filter.mp hw).2
  case right_inv =>
    intro d hd
    have hSc : d.1ᶜ.card = leaderPos m k := by
      have hcard : d.1.card = 2 * (k + 1) - 1 :=
        (Finset.mem_powersetCard.mp (Finset.mem_product.mp hd).1).2
      rw [Finset.card_compl, Fintype.card_fin, hcard]; unfold leaderPos; omega
    have hWmem := (Ncs_inv_mem m k hk β d.1 d.2.1 d.2.2 hd hSc).1
    have hWrc := (Ncs_inv_mem m k hk β d.1 d.2.1 d.2.2 hd hSc).2
    set W : Equiv.Perm (Fin (2 * (m + 1))) :=
      assemblePerm (2 * (m + 1)) (leaderPos m k) (by omega) (leaderPos_lt m k hk)
        d.1ᶜ hSc d.2.2 (btCastInv m k hk (d.2.1.trans Fin.revPerm)) with hWeq
    have hwdu : IsDownUp W := by
      have := hWmem; rw [downUpPerms] at this
      simpa only [Set.mem_toFinset, Set.mem_setOf_eq] using this
    have hmax : posOfMax (by omega) W = leaderPos m k :=
      rc_compSnoc_forward m k hk β W hwdu hWrc
    have hres := Ncs_right_inv m k hk β d.1 d.2.1 d.2.2 hd hSc W hWeq hwdu hmax
    -- goal: (i (j d)) = d, i.e. the disassembly triple of W equals d
    exact hres

/-- `blocksFun` of `compSnoc` at any index equals list access into `β.blocks ++ [k+1]`. -/
lemma compSnoc_blocksFun_val (m k : ℕ) (hk : k ≤ m) (β : Composition (m - k))
    (i : Fin (compSnoc m k hk β).length) (hlt : (i : ℕ) < (β.blocks ++ [k + 1]).length) :
    (compSnoc m k hk β).blocksFun i = (β.blocks ++ [k + 1])[(i : ℕ)] := by
  have h1 : (compSnoc m k hk β).blocksFun i
      = (compSnoc m k hk β).blocks[(i : ℕ)]'(by
          rw [(compSnoc m k hk β).blocks_length]; exact i.isLt) := rfl
  rw [h1]
  simp only [compSnoc_blocks]

/-- `rhsBinom` satisfies the same last-block recursion (pure arithmetic on the product). -/
lemma rhsBinom_compSnoc (m k : ℕ) (hk : k ≤ m) (β : Composition (m - k)) :
    rhsBinom (compSnoc m k hk β)
      = Nat.choose (2 * (m + 1) - 1) (2 * (k + 1) - 1)
          * euler (2 * (k + 1) - 1) * rhsBinom β := by
  have hlen : (compSnoc m k hk β).length = β.length + 1 := compSnoc_length m k hk β
  unfold rhsBinom
  -- reindex the product from `Fin (compSnoc.length)` to `Fin (β.length + 1)`
  rw [show (∏ i : Fin (compSnoc m k hk β).length,
            Nat.choose (2 * (compSnoc m k hk β).sizeUpTo ((i : ℕ) + 1) - 1)
                (2 * (compSnoc m k hk β).blocksFun i - 1)
              * euler (2 * (compSnoc m k hk β).blocksFun i - 1))
        = ∏ j : Fin (β.length + 1),
            Nat.choose (2 * (compSnoc m k hk β).sizeUpTo
                  ((Fin.cast hlen.symm j : ℕ) + 1) - 1)
                (2 * (compSnoc m k hk β).blocksFun (Fin.cast hlen.symm j) - 1)
              * euler (2 * (compSnoc m k hk β).blocksFun (Fin.cast hlen.symm j) - 1) from by
        rw [← Fin.prod_congr' _ hlen]
        apply Finset.prod_congr rfl
        intro i _; congr 1]
  rw [Fin.prod_univ_castSucc]
  -- last block value = k + 1 and its partial sum = m + 1
  have hlast_bf : (compSnoc m k hk β).blocksFun
      (Fin.cast hlen.symm (Fin.last β.length)) = k + 1 := by
    rw [compSnoc_blocksFun_val m k hk β _ (by simp [hlen])]
    simp [Fin.val_last]
  have hlast_su : (compSnoc m k hk β).sizeUpTo
      ((Fin.cast hlen.symm (Fin.last β.length) : ℕ) + 1) = m + 1 := by
    rw [Fin.coe_cast, Fin.val_last, compSnoc_sizeUpTo_last]
  have hhead : (∏ i : Fin β.length,
        Nat.choose (2 * (compSnoc m k hk β).sizeUpTo
              ((Fin.cast hlen.symm (Fin.castSucc i) : ℕ) + 1) - 1)
            (2 * (compSnoc m k hk β).blocksFun (Fin.cast hlen.symm (Fin.castSucc i)) - 1)
          * euler (2 * (compSnoc m k hk β).blocksFun (Fin.cast hlen.symm (Fin.castSucc i)) - 1))
      = (∏ i : Fin β.length,
          Nat.choose (2 * β.sizeUpTo ((i : ℕ) + 1) - 1) (2 * β.blocksFun i - 1)
            * euler (2 * β.blocksFun i - 1)) := by
    apply Finset.prod_congr rfl
    intro j _
    have hbf : (compSnoc m k hk β).blocksFun
        (Fin.cast hlen.symm (Fin.castSucc j)) = β.blocksFun j := by
      rw [compSnoc_blocksFun_val m k hk β _ (by
        simp only [Fin.coe_cast, Fin.coe_castSucc, List.length_append, List.length_singleton]
        have := j.isLt; rw [β.blocks_length]; omega)]
      rw [List.getElem_append_left (by rw [β.blocks_length]; simpa using j.isLt)]
      rfl
    have hsu : (compSnoc m k hk β).sizeUpTo
        ((Fin.cast hlen.symm (Fin.castSucc j) : ℕ) + 1) = β.sizeUpTo ((j : ℕ) + 1) := by
      rw [Fin.coe_cast, Fin.coe_castSucc, compSnoc_sizeUpTo_le m k hk β (by have := j.isLt; omega)]
    rw [hbf, hsu]
  rw [hlast_bf, hlast_su, hhead]
  ring

/-! ## Main Statement 1 (proofs relocated here, after the composition helpers) -/

/-- **Statement 1 (closed formula for `N(α)`), integer/binomial form.**
For every `n ≥ 1` and every composition `α ⊨ n`,
`N(α) = ∏_{j=1}^ℓ C(2 s_j - 1, 2 α_j - 1) E_{2 α_j - 1}`. -/
theorem N_eq_rhsBinom {n : ℕ} (hn : 1 ≤ n) (α : Composition n) :
    N α = rhsBinom α := by
  -- Strong induction on n, peeling the last block via `N_compSnoc` / `rhsBinom_compSnoc`.
  clear hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, α, ih with
    | 0, α, _ =>
      -- Composition 0 is empty; both N and rhsBinom reduce on `Composition.ones 0`.
      have hbl : α.blocks = (Composition.ones 0).blocks := by
        have hsum : α.blocks.sum = 0 := α.blocks_sum
        rcases List.eq_nil_or_concat α.blocks with h | ⟨l, a, h⟩
        · simp [h, Composition.ones]
        · exfalso
          have ha : a ∈ α.blocks := by rw [h]; simp
          have hap := α.blocks_pos ha
          have hle : a ≤ α.blocks.sum :=
            List.single_le_sum (fun x _ => Nat.zero_le x) _ ha
          omega
      rw [Composition.ext hbl]
      decide
    | (m + 1), α, ih =>
      -- last part and its predecessor
      set L := α.blocks.getLast (comp_blocks_ne_nil α) with hL
      have hLpos : 0 < L := α.blocks_pos (List.getLast_mem _)
      have hLle : L ≤ m + 1 := by
        calc L ≤ α.blocks.sum :=
              List.single_le_sum (fun x _ => Nat.zero_le x) _ (List.getLast_mem _)
          _ = m + 1 := α.blocks_sum
      have hk : L - 1 ≤ m := by omega
      -- rewrite α as compSnoc of its init
      have hblocks : (compSnoc m (L - 1) hk (compInit α)).blocks = α.blocks :=
        compSnoc_compInit_blocks α hk
      have hαeq : α = compSnoc m (L - 1) hk (compInit α) :=
        (Composition.ext hblocks).symm
      have hkL : (L - 1) + 1 = L := by omega
      rw [hαeq, N_compSnoc, rhsBinom_compSnoc]
      congr 1
      -- reduce to N (compInit α) = rhsBinom (compInit α) via the IH
      have hinit_size : m - (L - 1) < m + 1 := by omega
      exact ih (m - (L - 1)) hinit_size (compInit α)

/-- **Statement 1 (second, rational form).**
The same count equals `(2n)! ∏_{j=1}^ℓ b_{α_j} / s_j`, an identity of rational numbers. -/
theorem N_eq_rhsRat {n : ℕ} (hn : 1 ≤ n) (α : Composition n) :
    (N α : ℚ)
      = (Nat.factorial (2 * n)) *
          ∏ i : Fin α.length, bRat (α.blocksFun i) / (α.sizeUpTo (i + 1)) := by
  rw [N_eq_rhsBinom hn α]
  exact rhsBinom_eq_rhsRat hn α

theorem Sgen_psi_expansion (K : Type*) [Field K] [CharZero K] (n : ℕ) :
    Sgen K n = ∑ α : Composition n, ((sgenCoeff α : ℚ) : K) • PsiComp K α := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    match n with
    | 0 =>
      -- base case: unique empty composition
      rw [show Sgen K 0 = 1 by rw [Sgen]]
      have hlen0 : (Composition.ones 0).length = 0 := by
        rw [Composition.ones_length]
      rw [Finset.sum_eq_single (Composition.ones 0)]
      · rw [show sgenCoeff (Composition.ones 0) = 1 by
            unfold sgenCoeff
            apply Finset.prod_eq_one
            intro i _
            exact (Fin.cast hlen0 i).elim0]
        rw [show PsiComp K (Composition.ones 0) = 1 by
            unfold PsiComp
            simp [Composition.ones_blocks]]
        simp
      · intro b _ hb
        exfalso; apply hb
        apply Composition.ext
        have hb0 : b.blocks = [] := by
          by_contra hne
          obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil b.blocks hne
          have h1 := b.blocks_pos hx
          have h2 := List.single_le_sum (fun _ _ => Nat.zero_le _) x hx
          rw [b.blocks_sum] at h2
          omega
        rw [hb0, Composition.ones_blocks]; simp
      · intro h; exact absurd (Finset.mem_univ _) h
    | (m + 1) =>
      -- inductive step
      have hrec : Sgen K (m + 1)
          = (m + 1 : K)⁻¹ • ∑ k ∈ Finset.range (m + 1), Sgen K (m - k) * Psi K (k + 1) := by
        rw [Sgen]
      rw [hrec]
      -- expand each Sgen (m - k) by IH
      have hexp : ∀ k ∈ Finset.range (m + 1),
          Sgen K (m - k) * Psi K (k + 1)
            = ∑ β : Composition (m - k),
                ((sgenCoeff β : ℚ) : K) • (PsiComp K β * Psi K (k + 1)) := by
        intro k hk
        rw [IH (m - k) (by simp only [Finset.mem_range] at hk; omega)]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro β _
        rw [smul_mul_assoc]
      rw [Finset.sum_congr rfl hexp]
      -- Distribute the scalar (m+1)⁻¹ into both sums.
      simp only [Finset.smul_sum]
      -- Now each summand: (m+1)⁻¹ • (coeff β • (PsiComp β * Psi(k+1)))
      -- Rewrite it as coeff(compSnoc) • PsiComp(compSnoc), for k ≤ m.
      have hterm : ∀ (k : ℕ) (hkm : k ≤ m) (β : Composition (m - k)),
          (m + 1 : K)⁻¹ • (((sgenCoeff β : ℚ) : K) • (PsiComp K β * Psi K (k + 1)))
            = ((sgenCoeff (compSnoc m k hkm β) : ℚ) : K)
                • PsiComp K (compSnoc m k hkm β) := by
        intro k hkm β
        rw [PsiComp_compSnoc, smul_smul, sgenCoeff_compSnoc m k hkm β]
        congr 1
        push_cast
        ring
      -- Reindex: combine k-sum and β-sum into a sum over Composition (m+1).
      -- LHS: ∑ k ∈ range(m+1), ∑ β : Composition (m-k), (m+1)⁻¹ • coeff β • (...)
      -- RHS: ∑ α : Composition (m+1), coeff α • PsiComp α
      rw [Finset.sum_sigma']
      -- now a single sum over the sigma finset
      apply Finset.sum_bij'
        (i := fun x hx => compSnoc m x.1 (by
          simp only [Finset.mem_sigma, Finset.mem_range] at hx; omega) x.2)
        (j := fun α _ => ⟨α.blocks.getLast (comp_blocks_ne_nil α) - 1, compInit α⟩)
      case hi => -- maps into univ
        intro x hx; exact Finset.mem_univ _
      case hj => -- maps into the sigma finset
        intro α hα
        simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_univ, and_true]
        have hlast_le : α.blocks.getLast (comp_blocks_ne_nil α) ≤ m + 1 := by
          calc α.blocks.getLast (comp_blocks_ne_nil α)
              ≤ α.blocks.sum := List.single_le_sum (fun x _ => Nat.zero_le x) _
                (List.getLast_mem _)
            _ = m + 1 := α.blocks_sum
        have hlast_pos : 0 < α.blocks.getLast (comp_blocks_ne_nil α) :=
          α.blocks_pos (List.getLast_mem _)
        omega
      case left_neg => -- left inverse: j (i x) = x
        intro x hx
        simp only [Finset.mem_sigma, Finset.mem_range] at hx
        have hkm : x.1 ≤ m := by omega
        have hlast : (compSnoc m x.1 hkm x.2).blocks.getLast
            (comp_blocks_ne_nil _) = x.1 + 1 :=
          compSnoc_getLast m x.1 hkm x.2 _
        have hfst : (compSnoc m x.1 hkm x.2).blocks.getLast
            (comp_blocks_ne_nil _) - 1 = x.1 := by rw [hlast]; omega
        -- prove Sigma equality
        refine Sigma.ext hfst ?_
        exact Composition.heq_of_blocks _ _ (congrArg (fun t => m - t) hfst)
          (compInit_compSnoc_blocks m x.1 hkm x.2)
      case right_neg => -- right inverse: i (j α) = α
        intro α hα
        apply Composition.ext
        exact compSnoc_compInit_blocks α _
      case h => -- values match
        intro x hx
        exact hterm x.1 (by
          simp only [Finset.mem_sigma, Finset.mem_range] at hx; omega) x.2

/-- On a positive generator `φ_b` acts diagonally: `φ_b(Ψ_k) = b_k • Ψ_k` for `k ≥ 1`. -/
theorem phiB_Psi {K : Type*} [Field K] [CharZero K] {k : ℕ} (hk : k ≠ 0) :
    phiB K (Psi K k) = ((bRat k : ℚ) : K) • Psi K k := by
  simp only [Psi, if_neg hk, phiB, FreeAlgebra.lift_ι_apply]

/-- List version of `phiB_PsiComp`: for a list of positive parts. -/
theorem phiB_prod_list {K : Type*} [Field K] [CharZero K] (l : List ℕ)
    (hpos : ∀ k ∈ l, k ≠ 0) :
    phiB K ((l.map (Psi K)).prod) = (((l.map bRat).prod : ℚ) : K) • (l.map (Psi K)).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, List.map_cons, List.prod_cons]
    rw [phiB_Psi (hpos a (by simp)),
      ih (fun k hk => hpos k (List.mem_cons_of_mem a hk))]
    push_cast
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm]

/-- **Sub-lemma S2.2 (φ_b acts diagonally on the Ψ-basis).**
`φ_b(Ψ^α) = (∏_j b_{α_j}) • Ψ^α`.

Informal argument.  `φ_b` is the algebra homomorphism with `φ_b(Ψ_k) = b_k Ψ_k`
(`phiB` is `FreeAlgebra.lift K (fun k => (bRat k) • ι k)`, and for `k ≥ 1`,
`Psi K k = ι k`).  Since `Ψ^α = ∏_j Ψ_{α_j}` is a product of generators and `φ_b` is
multiplicative, `φ_b(Ψ^α) = ∏_j φ_b(Ψ_{α_j}) = ∏_j (b_{α_j} Ψ_{α_j})
= (∏_j b_{α_j}) · ∏_j Ψ_{α_j} = (∏_j b_{α_j}) Ψ^α` (scalars pull out and commute).
Formal: induct on `α.blocks` using `map_mul`/`map_prod` for `phiB`, `FreeAlgebra.lift_ι_apply`
for each generator, and `Algebra.smul_def`/`smul_mul_assoc` to collect the scalars.  Each
part `α_j ≥ 1` so `Psi K α_j = ι α_j` (the `k = 0` branch never occurs). -/
theorem phiB_PsiComp {K : Type*} [Field K] [CharZero K] {n : ℕ} (α : Composition n) :
    phiB K (PsiComp K α) = ((bLam (α.blocks : Multiset ℕ) : ℚ) : K) • PsiComp K α := by
  unfold PsiComp bLam
  rw [Multiset.map_coe, Multiset.prod_coe]
  exact phiB_prod_list α.blocks (fun k hk => (α.blocks_pos hk).ne')

/-- **Sub-lemma S2.3 (Ψ-expansion of `𝐀_n`).**
`𝐀_n = φ_b(S_n) = ∑_{α ⊨ n} (b_λ(α) · (∏_j s_j)⁻¹) • Ψ^α`, i.e. the coefficient of
`Ψ^α` is `bLam α.blocks · sgenCoeff α`.

Informal argument.  Apply `φ_b` to the expansion S2.1, use linearity (`map_sum`,
`map_smul`) and S2.2 termwise:
`𝐀_n = φ_b(∑_α c_α Ψ^α) = ∑_α c_α φ_b(Ψ^α) = ∑_α c_α (∏_j b_{α_j}) Ψ^α`,
with `c_α = sgenCoeff α`.  Combine the two scalars in `K` (both are images of rationals;
`CharZero` makes the ℚ→K coercion a ring hom that respects `*`). -/
theorem Anc_psi_expansion {K : Type*} [Field K] [CharZero K] (n : ℕ) :
    Anc K n = ∑ α : Composition n,
      (((bLam (α.blocks : Multiset ℕ) * sgenCoeff α : ℚ)) : K) • PsiComp K α := by
  unfold Anc
  rw [Sgen_psi_expansion, map_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [map_smul, phiB_PsiComp, smul_smul]
  congr 1
  push_cast
  ring

/-- Rational identity behind the coefficient match in Statement 2:
`(2n)! · (b_λ(α) · (∏_j s_j)⁻¹) = N(α)` as rationals.  This is exactly `N_eq_rhsRat`
rewritten with `bLam`/`sgenCoeff` in place of the explicit product. -/
theorem factorial_mul_coeff_eq_N {n : ℕ} (hn : 1 ≤ n) (α : Composition n) :
    (Nat.factorial (2 * n) : ℚ) * (bLam (α.blocks : Multiset ℕ) * sgenCoeff α)
      = (N α : ℚ) := by
  rw [N_eq_rhsRat hn α]
  congr 1
  -- bLam α.blocks * sgenCoeff α = ∏ i, bRat (α.blocksFun i) / (α.sizeUpTo (i+1))
  have hbLam : bLam (α.blocks : Multiset ℕ) = ∏ i : Fin α.length, bRat (α.blocksFun i) := by
    unfold bLam
    rw [Multiset.map_coe, Multiset.prod_coe, ← List.prod_ofFn]
    congr 1
    rw [← Composition.ofFn_blocksFun α, List.map_ofFn]
    rfl
  rw [hbLam]
  unfold sgenCoeff
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [div_eq_mul_inv]

/-! ## Main Statement 2 -/

/-- **Statement 2 (noncommutative symmetric function identity).**
For every `n ≥ 1`, in `NSym` one has
`(2n)! 𝐀_n = ∑_{α ⊨ n} N(α) Ψ^α`. -/
theorem factorial_smul_Anc_eq {K : Type*} [Field K] [CharZero K] {n : ℕ} (hn : 1 ≤ n) :
    (Nat.factorial (2 * n) : K) • Anc K n
      = ∑ α : Composition n, (N α : K) • PsiComp K α := by
  rw [Anc_psi_expansion, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro α _
  -- reduce to scalar equality in K
  rw [smul_smul]
  congr 1
  -- (2n)! * (image of bLam·sgenCoeff) = (N α : K); prove via the ℚ identity + CharZero
  have h := factorial_mul_coeff_eq_N hn α
  have hK := congrArg (fun q : ℚ => (q : K)) h
  push_cast at hK
  simpa using hK

/-- The image of `Ψ^α` under `χ` is the power-sum product `p_α` over the parts of `α`.

Informal argument.  `χ` (`chiMap`) is `FreeAlgebra.lift K (fun k => psym K k)`, so it is
multiplicative with `χ(Ψ_k) = p_k` (for `k ≥ 1`, `Psi K k = ι k`, and
`χ(ι k) = psym K k`).  Hence `χ(Ψ^α) = χ(∏_j Ψ_{α_j}) = ∏_j p_{α_j}
= psymLam K (α.blocks)`.  Formal: induct on `α.blocks`/use `map_prod`,
`FreeAlgebra.lift_ι_apply`. -/
theorem chi_Psi {K : Type*} [Field K] (k : ℕ) :
    chiMap K (Psi K k) = psym K k := by
  rcases eq_or_ne k 0 with hk | hk
  · simp [Psi, psym, hk]
  · simp only [Psi, psym, if_neg hk, chiMap, FreeAlgebra.lift_ι_apply]

theorem chi_PsiComp {K : Type*} [Field K] {n : ℕ} (α : Composition n) :
    chiMap K (PsiComp K α) = psymLam K (α.blocks : Multiset ℕ) := by
  unfold PsiComp psymLam
  rw [map_list_prod, List.map_map]
  rw [Multiset.map_coe, Multiset.prod_coe]
  congr 1
  apply List.map_congr_left
  intro k _
  simp only [Function.comp_apply, chi_Psi]

/- **Sub-lemma S2.4 (composition → partition regrouping).**
`∑_{α ⊨ n} (b_λ(α) · (∏_j s_j)⁻¹) p_{α}  =  ∑_{λ ⊢ n} z_λ⁻¹ b_λ p_λ = A_n`.

Informal argument.  Apply `χ` to `Anc_psi_expansion` and use `chi_PsiComp`:
`χ(𝐀_n) = ∑_{α ⊨ n} (b_λ(α)·sgenCoeff α) · p_{sort(α)}`, where `p_α` only depends on the
multiset of parts of `α`.  The key combinatorial identity is that grouping the
compositions `α` by their underlying partition `λ = sort(α)` gives
`∑_{α : sort(α)=λ} sgenCoeff α = z_λ⁻¹` for each partition `λ ⊢ n`.  (Equivalently, this
is the classical NSym→Sym fact `χ(S_n) = h_n` combined with
`h_n = ∑_{λ⊢n} z_λ⁻¹ p_λ`; the compositions-with-fixed-content refinement of the
`Ψ`-expansion of `S_n` collapses to the `z_λ⁻¹` normalisation.)  Since `b_λ(α)` and `p_α`
depend only on the content `λ`, the double sum collapses to
`∑_{λ⊢n} (∑_{α:content λ} sgenCoeff α) b_λ p_λ = ∑_{λ⊢n} z_λ⁻¹ b_λ p_λ = A_n`. -/
/-- The "content" partition of a composition: the multiset of its blocks. -/
def compContent {n : ℕ} (α : Composition n) : Nat.Partition n where
  parts := (α.blocks : Multiset ℕ)
  parts_pos := by
    intro i hi; simp only [Multiset.mem_coe] at hi; exact α.blocks_pos hi
  parts_sum := by
    show (α.blocks : Multiset ℕ).sum = n
    rw [Multiset.sum_coe]; exact α.blocks_sum

lemma compContent_parts {n : ℕ} (α : Composition n) :
    (compContent α).parts = (α.blocks : Multiset ℕ) := rfl

/-- `zLam` is positive (hence nonzero). -/
lemma zLam_pos (m : Multiset ℕ) (hpos : ∀ x ∈ m, 0 < x) : 0 < zLam m := by
  unfold zLam
  apply Finset.prod_pos
  intro i hi
  rw [Multiset.mem_toFinset] at hi
  have : 0 < i := hpos i hi
  positivity

/-- The zLam-erase relation: for `t ∈ m`, `zLam m = zLam (m.erase t) * (t * m.count t)`. -/
lemma zLam_erase {t : ℕ} {m : Multiset ℕ} (ht : t ∈ m) :
    zLam m = zLam (m.erase t) * ((t : ℚ) * (m.count t)) := by
  classical
  set c := m.count t with hc
  have hcpos : 0 < c := by rw [hc]; exact Multiset.count_pos.mpr ht
  -- factor function
  set f : ℕ → ℚ := fun i => (i : ℚ) ^ (m.count i) * (Nat.factorial (m.count i)) with hf
  set g : ℕ → ℚ := fun i => (i : ℚ) ^ ((m.erase t).count i) *
      (Nat.factorial ((m.erase t).count i)) with hg
  -- for i ≠ t, f i = g i
  have hfg : ∀ i, i ≠ t → f i = g i := by
    intro i hi
    simp only [hf, hg, Multiset.count_erase_of_ne hi]
  -- toFinset of erase in both cases is subset relation
  have htmem : t ∈ m.toFinset := Multiset.mem_toFinset.mpr ht
  -- split zLam m at t
  have hsplit_m : zLam m = f t * ∏ i ∈ m.toFinset.erase t, f i := by
    unfold zLam
    rw [← Finset.prod_erase_mul _ _ htmem]
    ring
  by_cases hc1 : c = 1
  · -- t is erased from toFinset
    have htnotin : t ∉ (m.erase t) := by
      rw [← Multiset.count_eq_zero, Multiset.count_erase_self]
      omega
    have htf : (m.erase t).toFinset = m.toFinset.erase t := by
      ext x
      simp only [Multiset.mem_toFinset, Finset.mem_erase]
      constructor
      · intro hx
        refine ⟨?_, ?_⟩
        · rintro rfl; exact htnotin hx
        · exact Multiset.mem_of_mem_erase hx
      · rintro ⟨hne, hxm⟩
        rw [Multiset.mem_erase_of_ne hne]; exact hxm
    have hz_erase : zLam (m.erase t) = ∏ i ∈ m.toFinset.erase t, g i := by
      unfold zLam; rw [htf]
    rw [hsplit_m, hz_erase]
    have hprodeq : ∏ i ∈ m.toFinset.erase t, f i = ∏ i ∈ m.toFinset.erase t, g i := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [Finset.mem_erase] at hi
      exact hfg i hi.1
    rw [hprodeq]
    have hft : f t = (t : ℚ) * c := by
      simp only [hf, ← hc, hc1]
      simp [Nat.factorial]
    rw [hft]; ring
  · -- t still in erase toFinset
    have hc2 : 2 ≤ c := by omega
    have htin : t ∈ (m.erase t) := by
      rw [← Multiset.count_pos, Multiset.count_erase_self]; omega
    have htf : (m.erase t).toFinset = m.toFinset := by
      ext x
      simp only [Multiset.mem_toFinset]
      constructor
      · intro hx; exact Multiset.mem_of_mem_erase hx
      · intro hx
        by_cases hxt : x = t
        · rw [hxt]; exact htin
        · rw [Multiset.mem_erase_of_ne hxt]; exact hx
    have htmem' : t ∈ (m.erase t).toFinset := Multiset.mem_toFinset.mpr htin
    have hz_erase : zLam (m.erase t) = g t * ∏ i ∈ m.toFinset.erase t, g i := by
      unfold zLam
      rw [htf, ← Finset.prod_erase_mul _ _ htmem]
      ring
    rw [hsplit_m, hz_erase]
    have hprodeq : ∏ i ∈ m.toFinset.erase t, f i = ∏ i ∈ m.toFinset.erase t, g i := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [Finset.mem_erase] at hi
      exact hfg i hi.1
    rw [hprodeq]
    -- now need: f t * P = g t * P * (t * c), i.e. f t = g t * (t * c)
    have hgt : (m.erase t).count t = c - 1 := by
      rw [Multiset.count_erase_self]
    have hft : f t = (t : ℚ) ^ c * (Nat.factorial c) := by simp [hf, ← hc]
    have hgtval : g t = (t : ℚ) ^ (c - 1) * (Nat.factorial (c - 1)) := by
      simp [hg, hgt]
    have hcpred : c - 1 + 1 = c := by omega
    have hcast : (Nat.factorial c : ℚ) = c * (Nat.factorial (c - 1)) := by
      conv_lhs => rw [← hcpred]
      rw [Nat.factorial_succ]
      push_cast [hcpred]; ring
    have hpow : (t : ℚ) ^ c = (t : ℚ) ^ (c - 1) * t := by
      conv_lhs => rw [← hcpred]
      rw [pow_succ]
    rw [hft, hgtval, hcast, hpow]; ring

/- **Key rational identity (fiber sum of `sgenCoeff`).**
For each partition `λ ⊢ n`, summing `sgenCoeff α = ∏_j 1/s_j(α)` over all compositions
`α` with content `λ` gives `z_λ⁻¹`. -/
/-- Erase a part `t ∈ lam.parts` from a partition `lam ⊢ n`, giving a partition of `n-t`. -/
def partErase {n : ℕ} (lam : Nat.Partition n) (t : ℕ) (ht : t ∈ lam.parts) :
    Nat.Partition (n - t) where
  parts := lam.parts.erase t
  parts_pos := by
    intro i hi
    exact lam.parts_pos (Multiset.mem_of_mem_erase hi)
  parts_sum := by
    have h := Multiset.sum_erase ht
    have := lam.parts_sum
    omega

lemma partErase_parts {n : ℕ} (lam : Nat.Partition n) (t : ℕ) (ht : t ∈ lam.parts) :
    (partErase lam t ht).parts = lam.parts.erase t := rfl

/-- Two partitions are equal iff their parts multisets are equal. -/
lemma Partition.eq_iff_parts {n : ℕ} (p q : Nat.Partition n) :
    p = q ↔ p.parts = q.parts := by
  constructor
  · rintro rfl; rfl
  · intro h; exact Nat.Partition.ext h

theorem sgenCoeff_fiber_sum {n : ℕ} (lam : Nat.Partition n) :
    (∑ α ∈ Finset.univ.filter (fun α : Composition n => compContent α = lam), sgenCoeff α)
      = (zLam lam.parts)⁻¹ := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  match n with
  | 0 =>
    -- only composition is the empty one; lam has empty parts
    have hlam : lam.parts = 0 := by
      have hsum := lam.parts_sum
      by_contra hne
      obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
      have hxpos := lam.parts_pos hx
      have := Multiset.single_le_sum (fun _ _ => Nat.zero_le _) x hx
      rw [hsum] at this; omega
    rw [show zLam lam.parts = 1 by rw [hlam]; simp [zLam]]
    simp only [inv_one]
    -- content of the empty composition equals lam
    have hcontent : ∀ α : Composition 0, compContent α = lam := by
      intro α
      rw [Partition.eq_iff_parts, compContent_parts, hlam]
      -- α.blocks sums to 0, so is empty
      have hb : α.blocks = [] := by
        by_contra hne
        obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil α.blocks hne
        have := List.single_le_sum (fun _ _ => Nat.zero_le _) x hx
        rw [α.blocks_sum] at this
        have := α.blocks_pos hx; omega
      rw [hb]; rfl
    have hfilter : (Finset.univ.filter (fun α : Composition 0 => compContent α = lam))
        = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro α _; exact hcontent α
    rw [hfilter]
    rw [Finset.sum_eq_single (Composition.ones 0)]
    · unfold sgenCoeff
      apply Finset.prod_eq_one
      intro i _
      have h0 : (Composition.ones 0).length = 0 := Composition.ones_length 0
      have hi := i.isLt
      omega
    · intro b _ hb
      exfalso; apply hb
      apply Composition.ext
      have hb0 : b.blocks = [] := by
        by_contra hne
        obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil b.blocks hne
        have := List.single_le_sum (fun _ _ => Nat.zero_le _) x hx
        rw [b.blocks_sum] at this
        have := b.blocks_pos hx; omega
      rw [hb0, Composition.ones_blocks]; simp
    · intro h; exact absurd (Finset.mem_univ _) h
  | (m + 1) =>
    -- Rewrite the filtered sum as a full sum with an `if`.
    rw [Finset.sum_filter]
    -- Summand on the sigma side.
    set F : ((k : Fin (m + 1)) × Composition (m - (k : ℕ))) → ℚ :=
      fun x => if compContent (compSnoc m (x.1 : ℕ) (by have := x.1.isLt; omega) x.2) = lam
        then sgenCoeff (compSnoc m (x.1 : ℕ) (by have := x.1.isLt; omega) x.2) else 0
      with hF
    -- Transform via the sigma-bijection (α ↔ (last block - 1, init)).
    have hbij : (∑ α : Composition (m + 1),
          (if compContent α = lam then sgenCoeff α else 0))
        = ∑ x : ((k : Fin (m + 1)) × Composition (m - (k : ℕ))), F x := by
      apply Finset.sum_bij'
        (i := fun α _ => ⟨⟨α.blocks.getLast (comp_blocks_ne_nil α) - 1, by
            have hlast_le : α.blocks.getLast (comp_blocks_ne_nil α) ≤ m + 1 := by
              calc α.blocks.getLast (comp_blocks_ne_nil α)
                  ≤ α.blocks.sum := List.single_le_sum (fun x _ => Nat.zero_le x) _
                    (List.getLast_mem _)
                _ = m + 1 := α.blocks_sum
            have hlast_pos : 0 < α.blocks.getLast (comp_blocks_ne_nil α) :=
              α.blocks_pos (List.getLast_mem _)
            omega⟩, compInit α⟩)
        (j := fun x _ => compSnoc m (x.1 : ℕ) (by have := x.1.isLt; omega) x.2)
      case hi => intro α _; exact Finset.mem_univ _
      case hj => intro x _; exact Finset.mem_univ _
      case left_neg =>
        intro α _
        apply Composition.ext
        exact compSnoc_compInit_blocks α _
      case right_neg =>
        intro x _
        have hkm : (x.1 : ℕ) ≤ m := by have := x.1.isLt; omega
        have hlast : (compSnoc m (x.1 : ℕ) hkm x.2).blocks.getLast
            (comp_blocks_ne_nil _) = (x.1 : ℕ) + 1 :=
          compSnoc_getLast m (x.1 : ℕ) hkm x.2 _
        have hfst : (compSnoc m (x.1 : ℕ) hkm x.2).blocks.getLast
            (comp_blocks_ne_nil _) - 1 = (x.1 : ℕ) := by rw [hlast]; omega
        refine Sigma.ext ?_ ?_
        · apply Fin.ext; simpa using hfst
        · exact Composition.heq_of_blocks _ _ (congrArg (fun t => m - t) hfst)
            (compInit_compSnoc_blocks m (x.1 : ℕ) hkm x.2)
      case h =>
        intro α _
        simp only [hF]
        have hkm : (α.blocks.getLast (comp_blocks_ne_nil α) - 1) ≤ m := by
          have hlast_le : α.blocks.getLast (comp_blocks_ne_nil α) ≤ m + 1 := by
            calc α.blocks.getLast (comp_blocks_ne_nil α)
                ≤ α.blocks.sum := List.single_le_sum (fun x _ => Nat.zero_le x) _
                  (List.getLast_mem _)
              _ = m + 1 := α.blocks_sum
          omega
        have hblocks : (compSnoc m (α.blocks.getLast (comp_blocks_ne_nil α) - 1) hkm
            (compInit α)).blocks = α.blocks := compSnoc_compInit_blocks α _
        have hcomp : compSnoc m (α.blocks.getLast (comp_blocks_ne_nil α) - 1) (by
            have := hkm; omega) (compInit α) = α := Composition.ext hblocks
        rw [hcomp]
    rw [hbij, hF]
    -- Split the sigma sum into nested sums over k and β.
    rw [Fintype.sum_sigma]
    -- Characterize when compContent (compSnoc ...) = lam.
    have hchar : ∀ (k : Fin (m + 1)) (hk : (k : ℕ) ≤ m) (β : Composition (m - (k : ℕ))),
        (compContent (compSnoc m (k : ℕ) hk β) = lam)
          ↔ ((k : ℕ) + 1 ∈ lam.parts ∧
              (β.blocks : Multiset ℕ) = lam.parts.erase ((k : ℕ) + 1)) := by
      intro k hk β
      rw [Partition.eq_iff_parts, compContent_parts, compSnoc_blocks]
      rw [show ((β.blocks ++ [(k : ℕ) + 1] : List ℕ) : Multiset ℕ)
            = ((k : ℕ) + 1) ::ₘ (β.blocks : Multiset ℕ) by
          rw [← Multiset.coe_add, Multiset.add_comm]
          rfl]
      constructor
      · intro h
        have hmem : (k : ℕ) + 1 ∈ lam.parts := by
          rw [← h]; exact Multiset.mem_cons_self _ _
        refine ⟨hmem, ?_⟩
        rw [← h, Multiset.erase_cons_head]
      · rintro ⟨hmem, hbl⟩
        rw [hbl, Multiset.cons_erase hmem]
    -- Evaluate the inner sum for each k.
    have hinner : ∀ k : Fin (m + 1),
        (∑ β : Composition (m - (k : ℕ)),
            (if compContent (compSnoc m (k : ℕ) (by have := k.isLt; omega) β) = lam
              then sgenCoeff (compSnoc m (k : ℕ) (by have := k.isLt; omega) β) else 0))
          = (if (k : ℕ) + 1 ∈ lam.parts
              then (m + 1 : ℚ)⁻¹ * (zLam (lam.parts.erase ((k : ℕ) + 1)))⁻¹ else 0) := by
      intro k
      have hk : (k : ℕ) ≤ m := by have := k.isLt; omega
      by_cases hmem : (k : ℕ) + 1 ∈ lam.parts
      · rw [if_pos hmem]
        -- A partition of `m - k` whose parts are `lam.parts.erase (k+1)`.
        set lamE : Nat.Partition (m - (k : ℕ)) :=
          { parts := lam.parts.erase ((k : ℕ) + 1)
            parts_pos := by
              intro i hi
              exact lam.parts_pos (Multiset.mem_of_mem_erase hi)
            parts_sum := by
              have h := Multiset.sum_erase hmem
              have h2 := lam.parts_sum
              omega } with hlamE
        have hpart : lamE.parts = lam.parts.erase ((k : ℕ) + 1) := rfl
        have hsum1 : (∑ β : Composition (m - (k : ℕ)),
            (if compContent (compSnoc m (k : ℕ) hk β) = lam
              then sgenCoeff (compSnoc m (k : ℕ) hk β) else 0))
            = ∑ β : Composition (m - (k : ℕ)),
                (if compContent β = lamE
                  then sgenCoeff β * (m + 1 : ℚ)⁻¹ else 0) := by
          apply Finset.sum_congr rfl
          intro β _
          rw [sgenCoeff_compSnoc]
          congr 1
          apply propext
          rw [hchar k hk β]
          constructor
          · rintro ⟨_, hbl⟩
            rw [Partition.eq_iff_parts, compContent_parts, hpart, hbl]
          · intro h
            refine ⟨hmem, ?_⟩
            rw [Partition.eq_iff_parts, compContent_parts, hpart] at h
            exact h
        rw [hsum1, ← Finset.sum_filter]
        rw [show (∑ β ∈ Finset.univ.filter
              (fun β : Composition (m - (k : ℕ)) =>
                compContent β = lamE), sgenCoeff β * (m + 1 : ℚ)⁻¹)
            = (∑ β ∈ Finset.univ.filter
                (fun β : Composition (m - (k : ℕ)) =>
                  compContent β = lamE), sgenCoeff β)
                * (m + 1 : ℚ)⁻¹ from (Finset.sum_mul _ _ _).symm]
        rw [IH (m - (k : ℕ)) (by omega) lamE]
        rw [hpart]
        ring
      · rw [if_neg hmem]
        apply Finset.sum_eq_zero
        intro β _
        rw [if_neg]
        rw [hchar k hk β]
        rintro ⟨h, _⟩; exact hmem h
    rw [Finset.sum_congr rfl (fun k _ => hinner k)]
    -- lam.parts is positive, so zLam ≠ 0.
    have hlampos : ∀ x ∈ lam.parts, 0 < x := fun x hx => lam.parts_pos hx
    have hz : zLam lam.parts ≠ 0 := ne_of_gt (zLam_pos _ hlampos)
    -- Rewrite zLam(erase t)⁻¹ using zLam_erase.
    have hval : ∀ k : Fin (m + 1),
        (if (k : ℕ) + 1 ∈ lam.parts
            then (m + 1 : ℚ)⁻¹ * (zLam (lam.parts.erase ((k : ℕ) + 1)))⁻¹ else 0)
          = (if (k : ℕ) + 1 ∈ lam.parts
              then (m + 1 : ℚ)⁻¹ * (zLam lam.parts)⁻¹ *
                ((((k : ℕ) + 1 : ℚ)) * (lam.parts.count ((k : ℕ) + 1))) else 0) := by
      intro k
      by_cases hmem : (k : ℕ) + 1 ∈ lam.parts
      · rw [if_pos hmem, if_pos hmem]
        have herase := zLam_erase (t := (k : ℕ) + 1) (m := lam.parts) hmem
        have herase_ne : zLam (lam.parts.erase ((k : ℕ) + 1)) ≠ 0 := by
          apply ne_of_gt
          apply zLam_pos
          intro x hx
          exact lam.parts_pos (Multiset.mem_of_mem_erase hx)
        have hfac_ne : (((k : ℕ) + 1 : ℚ) * (lam.parts.count ((k : ℕ) + 1))) ≠ 0 := by
          have hc : 0 < lam.parts.count ((k : ℕ) + 1) := Multiset.count_pos.mpr hmem
          have : (0 : ℚ) < ((k : ℕ) + 1 : ℚ) * (lam.parts.count ((k : ℕ) + 1)) := by
            positivity
          exact ne_of_gt this
        have hcount_ne : (lam.parts.count ((k : ℕ) + 1) : ℚ) ≠ 0 := by
          have hc : 0 < lam.parts.count ((k : ℕ) + 1) := Multiset.count_pos.mpr hmem
          exact_mod_cast hc.ne'
        have key : (zLam lam.parts)⁻¹
              * ((((k : ℕ) + 1 : ℚ)) * (lam.parts.count ((k : ℕ) + 1)))
            = (zLam (lam.parts.erase ((k : ℕ) + 1)))⁻¹ := by
          rw [herase, mul_inv]
          push_cast
          field_simp
        rw [mul_assoc, key]
      · rw [if_neg hmem, if_neg hmem]
    rw [Finset.sum_congr rfl (fun k _ => hval k)]
    -- Factor out the constant (m+1)⁻¹ * zLam⁻¹.
    rw [← Finset.sum_filter]
    rw [show (∑ k ∈ Finset.univ.filter (fun k : Fin (m + 1) => (k : ℕ) + 1 ∈ lam.parts),
            (m + 1 : ℚ)⁻¹ * (zLam lam.parts)⁻¹ *
              (((k : ℕ) + 1 : ℚ) * (lam.parts.count ((k : ℕ) + 1))))
        = (m + 1 : ℚ)⁻¹ * (zLam lam.parts)⁻¹ *
            (∑ k ∈ Finset.univ.filter (fun k : Fin (m + 1) => (k : ℕ) + 1 ∈ lam.parts),
              (((k : ℕ) + 1 : ℚ) * (lam.parts.count ((k : ℕ) + 1)))) from by
        rw [Finset.mul_sum]]
    -- The filtered sum over k equals lam.parts.sum = m + 1.
    have hsumk : (∑ k ∈ Finset.univ.filter (fun k : Fin (m + 1) => (k : ℕ) + 1 ∈ lam.parts),
            (((k : ℕ) + 1 : ℚ) * (lam.parts.count ((k : ℕ) + 1))))
          = ((m + 1 : ℕ) : ℚ) := by
      have hbij : (∑ k ∈ Finset.univ.filter (fun k : Fin (m + 1) => (k : ℕ) + 1 ∈ lam.parts),
              (((k : ℕ) + 1 : ℚ) * (lam.parts.count ((k : ℕ) + 1))))
            = ∑ t ∈ lam.parts.toFinset, ((t : ℚ) * (lam.parts.count t)) := by
        refine Finset.sum_bij'
          (i := fun (k : Fin (m + 1)) _ => (k : ℕ) + 1)
          (j := fun (t : ℕ) ht => (⟨t - 1, by
            simp only [Finset.mem_filter, Finset.mem_univ, Multiset.mem_toFinset,
              true_and] at ht
            have hle : t ≤ m + 1 := by
              have := lam.parts_sum
              have hmem := Multiset.single_le_sum (fun _ _ => Nat.zero_le _) t ht
              omega
            have hpos := lam.parts_pos ht
            omega⟩ : Fin (m + 1)))
          ?_ ?_ ?_ ?_ ?_
        · intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          exact Multiset.mem_toFinset.mpr hk
        · intro t ht
          simp only [Finset.mem_filter, Finset.mem_univ, Multiset.mem_toFinset,
            true_and] at ht
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hpos := lam.parts_pos ht
          rw [show (t - 1) + 1 = t by omega]
          exact ht
        · intro k hk
          apply Fin.ext
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          have hpos := lam.parts_pos hk
          simp only [Nat.add_sub_cancel]
        · intro t ht
          simp only [Finset.mem_filter, Finset.mem_univ, Multiset.mem_toFinset,
            true_and] at ht
          have hpos := lam.parts_pos ht
          simp only
          omega
        · intro k hk
          push_cast
          ring
      rw [hbij]
      have hcard : (∑ t ∈ lam.parts.toFinset, ((t : ℚ) * (lam.parts.count t)))
          = ((lam.parts.sum : ℕ) : ℚ) := by
        rw [Finset.sum_multiset_count lam.parts]
        push_cast
        apply Finset.sum_congr rfl
        intro t _
        rw [nsmul_eq_mul]
        push_cast
        ring
      rw [hcard, lam.parts_sum]
    rw [hsumk]
    have hm1 : ((m + 1 : ℕ) : ℚ) = (m : ℚ) + 1 := by push_cast; ring
    rw [hm1]
    have hm1ne : ((m : ℚ) + 1) ≠ 0 := by positivity
    field_simp

theorem chi_Anc_regroup {K : Type*} [Field K] [CharZero K] (n : ℕ) :
    (∑ α : Composition n,
        (((bLam (α.blocks : Multiset ℕ) * sgenCoeff α : ℚ)) : K) •
          psymLam K (α.blocks : Multiset ℕ))
      = Asym K n := by
  rw [Asym]
  rw [← Finset.sum_fiberwise (Finset.univ) compContent
        (fun α : Composition n =>
          (((bLam (α.blocks : Multiset ℕ) * sgenCoeff α : ℚ)) : K) •
            psymLam K (α.blocks : Multiset ℕ))]
  apply Finset.sum_congr rfl
  intro lam _
  have hcongr : ∀ α ∈ Finset.univ.filter (fun α : Composition n => compContent α = lam),
      (((bLam (α.blocks : Multiset ℕ) * sgenCoeff α : ℚ)) : K) •
          psymLam K (α.blocks : Multiset ℕ)
        = (((bLam lam.parts * sgenCoeff α : ℚ)) : K) • psymLam K lam.parts := by
    intro α hα
    simp only [Finset.mem_filter] at hα
    have hb : (α.blocks : Multiset ℕ) = lam.parts := by
      rw [← compContent_parts α, hα.2]
    rw [hb]
  rw [Finset.sum_congr rfl hcongr, ← Finset.sum_smul]
  congr 1
  have hscal : (∑ α ∈ Finset.univ.filter (fun α : Composition n => compContent α = lam),
            ((bLam lam.parts * sgenCoeff α : ℚ))) = (zLam lam.parts)⁻¹ * bLam lam.parts := by
    rw [← Finset.mul_sum, sgenCoeff_fiber_sum lam]; ring
  rw [← hscal]
  push_cast
  rfl

/-- **Statement 2 (image under `χ`).**
For every `n ≥ 1`, `χ(𝐀_n) = A_n` in `Sym`. -/
theorem chi_Anc_eq {K : Type*} [Field K] [CharZero K] {n : ℕ} (hn : 1 ≤ n) :
    chiMap K (Anc K n) = Asym K n := by
  rw [Anc_psi_expansion, map_sum]
  simp only [map_smul, chi_PsiComp]
  exact chi_Anc_regroup n

/-! ## Correctness / characterization statements

These pin down the auxiliary definitions above as the intended mathematical objects. -/

/-- `euler` matches the initial values of the Euler (zigzag) numbers (OEIS A000111). -/
theorem euler_values :
    (List.range 10).map euler = [1, 1, 1, 2, 5, 16, 61, 272, 1385, 7936] := by
  simp only [List.range, List.range.loop, List.map]
  norm_num [euler, entringer]


/-- Worked example (Definition 6 / Notes): for
`w = 7 2 5 4 8 3 10 6 9 1 ∈ 𝒜_{10}` (here `n = 5`), one has `rc(ŵ) = (2,1,2)`.
In `0`-indexed values, `w` sends positions `0..9` to `6,1,4,3,7,2,9,5,8,0`. -/
def wex : Equiv.Perm (Fin (2 * 5)) :=
  Equiv.mk (fun i => ![6, 1, 4, 3, 7, 2, 9, 5, 8, 0] i)
    (fun i => ![9, 1, 5, 3, 2, 7, 0, 4, 8, 6] i) (by decide) (by decide)

theorem wex_isDownUp : IsDownUp wex := by decide

theorem rc_worked_example : (rc wex).blocks = [2, 1, 2] := by
  have hcex : (⟨[2,1,2], by decide, by decide⟩ : Composition 5).toCompositionAsSet
      = rcAsSet wex := by
    rw [CompositionAsSet.ext_iff]
    show (⟨[2,1,2], by decide, by decide⟩ : Composition 5).toCompositionAsSet.boundaries
      = recBoundaries wex
    decide
  have : (rc wex).blocks = (rcAsSet wex).toComposition.blocks := rfl
  rw [this, ← hcex, CompositionAsSet.toComposition_blocks,
    Composition.toCompositionAsSet_blocks]
