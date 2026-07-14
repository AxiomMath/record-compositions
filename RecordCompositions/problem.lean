import Mathlib
set_option backward.isDefEq.respectTransparency false

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

/-! ## Main Statement 1 -/

/-- **Statement 1 (closed formula for `N(α)`), integer/binomial form.**
For every `n ≥ 1` and every composition `α ⊨ n`,
`N(α) = ∏_{j=1}^ℓ C(2 s_j - 1, 2 α_j - 1) E_{2 α_j - 1}`. -/
theorem N_eq_rhsBinom {n : ℕ} (hn : 1 ≤ n) (α : Composition n) :
    N α = rhsBinom α := by
  sorry

/-- **Statement 1 (second, rational form).**
The same count equals `(2n)! ∏_{j=1}^ℓ b_{α_j} / s_j`, an identity of rational numbers. -/
theorem N_eq_rhsRat {n : ℕ} (hn : 1 ≤ n) (α : Composition n) :
    (N α : ℚ)
      = (Nat.factorial (2 * n)) *
          ∏ i : Fin α.length, bRat (α.blocksFun i) / (α.sizeUpTo (i + 1)) := by
  sorry

/-! ## Main Statement 2 -/

/-- **Statement 2 (noncommutative symmetric function identity).**
For every `n ≥ 1`, in `NSym` one has
`(2n)! 𝐀_n = ∑_{α ⊨ n} N(α) Ψ^α`. -/
theorem factorial_smul_Anc_eq {K : Type*} [Field K] [CharZero K] {n : ℕ} (hn : 1 ≤ n) :
    (Nat.factorial (2 * n) : K) • Anc K n
      = ∑ α : Composition n, (N α : K) • PsiComp K α := by
  sorry

/-- **Statement 2 (image under `χ`).**
For every `n ≥ 1`, `χ(𝐀_n) = A_n` in `Sym`. -/
theorem chi_Anc_eq {K : Type*} [Field K] [CharZero K] {n : ℕ} (hn : 1 ≤ n) :
    chiMap K (Anc K n) = Asym K n := by
  sorry

/-! ## Correctness / characterization statements

These pin down the auxiliary definitions above as the intended mathematical objects. -/

/-- `euler` matches the initial values of the Euler (zigzag) numbers (OEIS A000111). -/
theorem euler_values :
    (List.range 10).map euler = [1, 1, 1, 2, 5, 16, 61, 272, 1385, 7936] := by
  sorry

/-- `euler` satisfies the standard zigzag recurrence
`2 E_{n+2} = ∑_{k=0}^{n+1} C(n+1, k) E_k E_{n+1-k}`. -/
theorem euler_recurrence (n : ℕ) :
    2 * euler (n + 2)
      = ∑ k ∈ Finset.range (n + 2),
          Nat.choose (n + 1) k * euler k * euler (n + 1 - k) := by
  sorry

/-- Consistency of the two product forms in Statement 1 (as rationals):
`∏_j C(2 s_j - 1, 2 α_j - 1) E_{2 α_j - 1} = (2n)! ∏_j b_{α_j} / s_j`. -/
theorem rhsBinom_eq_rhsRat {n : ℕ} (hn : 1 ≤ n) (α : Composition n) :
    (rhsBinom α : ℚ)
      = (Nat.factorial (2 * n)) *
          ∏ i : Fin α.length, bRat (α.blocksFun i) / (α.sizeUpTo (i + 1)) := by
  sorry

/-- Worked example (Definition 6 / Notes): for
`w = 7 2 5 4 8 3 10 6 9 1 ∈ 𝒜_{10}` (here `n = 5`), one has `rc(ŵ) = (2,1,2)`.
In `0`-indexed values, `w` sends positions `0..9` to `6,1,4,3,7,2,9,5,8,0`. -/
def wex : Equiv.Perm (Fin (2 * 5)) :=
  Equiv.mk (fun i => ![6, 1, 4, 3, 7, 2, 9, 5, 8, 0] i)
    (fun i => ![9, 1, 5, 3, 2, 7, 0, 4, 8, 6] i) (by decide) (by decide)

theorem wex_isDownUp : IsDownUp wex := by decide

theorem rc_worked_example : (rc wex).blocks = [2, 1, 2] := by
  sorry
