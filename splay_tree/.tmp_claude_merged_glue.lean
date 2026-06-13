/- PUBLICATION HEADER
  Splay Deque — inverse-Ackermann arithmetic backbone (telescope engine)

  Public result: recursionTelescopedBound_abstract — a per-level-flat recurrence with
  O(alpha) recursion depth telescopes to c*n*alpha(n). Ports the gammaOf / poly-alpha
  collapse (gamma_poly_alpha_proved) over the shared Challenges.ZBK base so it is
  referenceable from the deque development. Axioms: {propext, Classical.choice, Quot.sound}.
-/

/-
§GLUE — the codex_ds recursion-telescope engine, ported into the ZBK base so it
is referenceable from `turn_main` (which itself imports only `Challenges.ZBK`).

This file imports `Challenges.ZBK` (the same base `turn_main` uses), which
transitively exposes the full `KlazarAckermann` Ackermann theory
(`F`, `F_omega`, `P_omega`, `alpha`).  On top of that base it re-derives the
exact `gammaOf`/`AckermannFacts`/`RecurrenceTelescope` machinery that lives in
the sibling scratch `.tmp_codex_ds_main.lean` (namespace `CodexDS`) — which is
NOT lake-importable because it has no module path.

The capstone is `GlueTelescope.recursion_telescope`: the abstract
per-level-flat-recurrence ⟹ `C·n·alpha(n+1) + C'·n` bound, now living in a base
that `turn_main` can see.  We additionally provide
`recursionTelescopedBound_abstract`, which is the exact `turn_main`
`RecursionTelescopedBound` conclusion `T n ≤ C·(n·alpha n) + C'·n` (note:
`alpha n`, not `alpha (n+1)`) for an arbitrary size-indexed touched-sum `T`,
given the W-D recurrence (`RecBase` + `RecStep`) for the squaring schedule.
Wiring this against the concrete `T n = Σ_{i<n} tpLenN init X i` and the
(residual-conditional) concrete `RecStep` discharges `RecursionTelescopedBound`
inside `turn_main`.
-/
import Challenges.ZBK

namespace GlueTelescope

open Classical
open KlazarAckermann

/-! ## Ported: direct Ackermann/alpha facts (CodexDS.AckermannFacts, verbatim) -/

namespace AckermannFacts

-- from dsv
lemma F_omega_exists (n : ℕ) : ∃ m, n ≤ F_omega m := by
  induction n with
  | zero =>
      use 0
      simp [F_omega, F]
  | succ n _ih =>
      use n + 1
      have := @F_inflationary (n + 1) (n + 1) (by omega) (by omega)
      rw [← F_omega] at this
      linarith

-- from dsv
lemma F_one (n : ℕ) : F 1 n = 2 * n := by
  rfl

-- from dsv
lemma F_succ_succ (k n : ℕ) : F (k + 2) n = (F (k + 1) ·)^[n] 1 := by
  rfl

-- from dsv
lemma iterate_ge_one {k m : ℕ} (hk : 1 ≤ k) :
    1 ≤ (F k ·)^[m] 1 := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
      rw [show (F k ·)^[m + 1] 1 = F k ((F k ·)^[m] 1) by
        rw [Function.iterate_succ_apply']]
      exact F_iterate_ge_one hk ih

-- from dsv
lemma iterate_step_ge {k n : ℕ} (hk : 1 ≤ k) :
    (F k ·)^[n] 1 ≤ (F k ·)^[n + 1] 1 := by
  rw [Function.iterate_succ_apply']
  have h_ge : 1 ≤ (F k ·)^[n] 1 := iterate_ge_one hk
  have h_inf : (F k ·)^[n] 1 < F k ((F k ·)^[n] 1) :=
    F_inflationary hk h_ge
  linarith

-- from dsv
lemma iterate_le_iterate_of_le {k a b : ℕ} (hk : 1 ≤ k) (hab : a ≤ b) :
    (F k ·)^[a] 1 ≤ (F k ·)^[b] 1 := by
  induction b generalizing a with
  | zero =>
      have ha0 : a = 0 := by linarith
      rw [ha0]
  | succ b ih =>
      by_cases h : a ≤ b
      · have h1 : (F k ·)^[a] 1 ≤ (F k ·)^[b] 1 := ih h
        have h2 : (F k ·)^[b] 1 ≤ (F k ·)^[b + 1] 1 := iterate_step_ge hk
        linarith
      · have ha1 : a = b + 1 := by linarith
        rw [ha1]

-- from dsv
lemma F_mono_right : ∀ k, 1 ≤ k → ∀ {a b : ℕ}, a ≤ b → F k a ≤ F k b := by
  intro k hk a b hab
  cases k with
  | zero => contradiction
  | succ k =>
      by_cases hk0 : k = 0
      · subst hk0
        simp [F]
        omega
      · have k_ge_1 : k ≥ 1 := by omega
        simp [F]
        exact iterate_le_iterate_of_le k_ge_1 hab

-- from dsv
lemma F_k_1_eq_2 {k : ℕ} (hk : 1 ≤ k) : F k 1 = 2 := by
  induction k with
  | zero => contradiction
  | succ k ih =>
      by_cases hk0 : k = 0
      · subst hk0
        rfl
      · have k_ge_1 : k ≥ 1 := by omega
        have : F (k + 1) 1 = F k 1 := by simp [F]
        rw [this]
        exact ih k_ge_1

-- from dsv
lemma F_k_n_le_iterate {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    F k n ≤ (F k ·)^[n] 1 := by
  induction n with
  | zero => linarith
  | succ n ih =>
      cases n with
      | zero =>
          simp [F_k_1_eq_2 hk]
      | succ n =>
          have h_iter : (F k ·)^[n + 2] 1 =
              F k ((F k ·)^[n + 1] 1) := by
            rw [Function.iterate_succ_apply']
          have h_n2 : n + 2 ≤ F k (n + 1) := by
            have h_inf : n + 1 < F k (n + 1) :=
              F_inflationary hk (by linarith)
            linarith
          have h_F2 : F k (n + 2) ≤ F k (F k (n + 1)) :=
            F_mono_right k hk (by omega)
          have h_ih : F k (n + 1) ≤ (F k ·)^[n + 1] 1 :=
            ih (by linarith)
          have h_F : F k (F k (n + 1)) ≤
              F k ((F k ·)^[n + 1] 1) :=
            F_mono_right k hk h_ih
          rw [h_iter]
          linarith

-- from dsv
lemma F_mono_left :
    ∀ {j k : ℕ}, 1 ≤ j → j ≤ k → ∀ n, 1 ≤ n → F j n ≤ F k n := by
  intro j k hj hjk n hn
  have h_base : F j n ≤ F j n := le_rfl
  have h_step :
      ∀ (m : ℕ), j ≤ m → F j n ≤ F m n → F j n ≤ F (m + 1) n := by
    intro m hm ih
    have h_kn : F m n ≤ F (m + 1) n := by
      cases m with
      | zero =>
          have h_j0 : j = 0 := by omega
          omega
      | succ m =>
          have hk' : 1 ≤ m + 1 := by omega
          simp [F]
          exact F_k_n_le_iterate hk' hn
    linarith
  exact Nat.le_induction h_base h_step k hjk

-- from dsv
lemma F_omega_zero : F_omega 0 = 0 := by
  rw [F_omega, F]

-- from dsv
lemma alpha_zero_eq : alpha 0 = 0 := by
  have h1 : alpha 0 ≤ 0 := by
    unfold alpha
    apply Nat.find_le
    unfold P_omega
    simp [F_omega_zero]
  have h2 : 0 ≤ alpha 0 := by simp
  omega

-- from dsv
lemma F_omega_mono : ∀ {a b : ℕ}, 1 ≤ a → a ≤ b → F_omega a ≤ F_omega b := by
  intro a b ha hab
  rw [F_omega, F_omega]
  have h3 : F a a ≤ F b a := F_mono_left ha hab a ha
  have h4 : F b a ≤ F b b := F_mono_right b (by omega) hab
  linarith

theorem alpha_spec (n : ℕ) :
    n ≤ F_omega (alpha n) := by
  change P_omega n (alpha n)
  unfold alpha
  exact @Nat.find_spec (P_omega n) (P_omega_decidable n) _

theorem alpha_min {n m : ℕ} (h : n ≤ F_omega m) :
    alpha n ≤ m := by
  change @Nat.find (P_omega n) (P_omega_decidable n) _ ≤ m
  exact @Nat.find_min' (P_omega n) (P_omega_decidable n) _ m h

theorem alpha_le_iff_exists_le (n m : ℕ) :
    alpha n ≤ m ↔ ∃ r ≤ m, n ≤ F_omega r := by
  change @Nat.find (P_omega n) (P_omega_decidable n) _ ≤ m ↔ ∃ r ≤ m, P_omega n r
  exact @Nat.find_le_iff (P_omega n) (P_omega_decidable n) _ m

theorem alpha_Fomega_le (m : ℕ) :
    alpha (F_omega m) ≤ m :=
  alpha_min (n := F_omega m) (m := m) le_rfl

theorem alpha_le_of_le_Fomega {n m : ℕ} (h : n ≤ F_omega m) :
    alpha n ≤ m :=
  alpha_min h

theorem alpha_zero_eq_zero :
    alpha 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact alpha_min (n := 0) (m := 0) (by simp)

theorem alpha_one_le_one :
    alpha 1 ≤ 1 := by
  apply alpha_min (n := 1) (m := 1)
  unfold F_omega KlazarAckermann.F
  norm_num

theorem one_le_Fomega_self {m : ℕ} (hm : 1 ≤ m) :
    1 ≤ F_omega m := by
  exact KlazarAckermann.F_iterate_ge_one (k := m) (n := m) hm hm

theorem Fomega_inflationary {m : ℕ} (hm : 1 ≤ m) :
    m < F_omega m := by
  exact KlazarAckermann.F_inflationary (k := m) (n := m) hm hm

theorem alpha_succ_le_self_of_Fomega_ge {n m : ℕ}
    (h : n + 1 ≤ F_omega m) :
    alpha (n + 1) ≤ m :=
  alpha_min h

theorem alpha_le_self_add_one (n : ℕ) :
    alpha n ≤ n + 1 := by
  apply alpha_min (n := n) (m := n + 1)
  cases n with
  | zero =>
      simp
  | succ n =>
      have hlt :
          n + 2 < F_omega (n + 2) := by
        exact Fomega_inflationary (m := n + 2) (by omega)
      have hle : n + 1 ≤ F_omega (n + 2) := by omega
      simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hle

-- from dsv
lemma alpha_le_iff (n m : ℕ) : alpha n ≤ m ↔ n ≤ F_omega m := by
  constructor
  · intro h
    have h_n_le : n ≤ F_omega (alpha n) := by
      have h_spec := Nat.find_spec (@F_omega_exists n)
      have h_eq :
          alpha n =
            @Nat.find (P_omega n) (P_omega_decidable n) (F_omega_exists n) := by
        unfold alpha
        rfl
      rw [h_eq]
      exact h_spec
    have h_Fmono : F_omega (alpha n) ≤ F_omega m := by
      by_cases hn0 : n = 0
      · subst hn0
        rw [alpha_zero_eq] at h
        rw [alpha_zero_eq, F_omega_zero]
        linarith
      · have h1 : 1 ≤ alpha n := by
          have : alpha n ≠ 0 := by
            by_contra h0
            rw [h0] at h_n_le
            rw [F_omega_zero] at h_n_le
            omega
          omega
        apply F_omega_mono h1 h
    linarith
  · intro h
    unfold alpha
    apply Nat.find_le
    unfold P_omega
    exact h

-- from dsv
lemma alpha_mono : ∀ {a b : ℕ}, a ≤ b → alpha a ≤ alpha b := by
  intro a b hab
  by_cases ha0 : a = 0
  · subst ha0
    rw [alpha_zero_eq]
    simp
  · have h_alpha_a_1 : 1 ≤ alpha a := by
      have : alpha a ≠ 0 := by
        by_contra h0
        have h_spec : a ≤ F_omega (alpha a) := by
          have h_spec := Nat.find_spec (F_omega_exists a)
          have h_eq :
              alpha a =
                @Nat.find (P_omega a) (P_omega_decidable a) (F_omega_exists a) := by
            unfold alpha
            rfl
          rw [h_eq]
          exact h_spec
        rw [h0] at h_spec
        rw [F_omega_zero] at h_spec
        omega
      omega
    apply (alpha_le_iff a (alpha b)).mpr
    have h_b_le : b ≤ F_omega (alpha b) := by
      have h_spec := Nat.find_spec (F_omega_exists b)
      have h_eq :
          alpha b =
            @Nat.find (P_omega b) (P_omega_decidable b) (F_omega_exists b) := by
        unfold alpha
        rfl
      rw [h_eq]
      exact h_spec
    linarith

-- from dsv
lemma alpha_F_omega_self (m : ℕ) : alpha (F_omega m) ≤ m := by
  unfold alpha
  apply Nat.find_le
  unfold P_omega
  exact le_rfl

-- from dsv
lemma alpha_pos_of_two_le {n : ℕ} : 2 ≤ n → 1 ≤ alpha n := by
  intro h
  have : n ≠ 0 := by linarith
  have : alpha n ≠ 0 := by
    by_contra h0
    have h_spec : n ≤ F_omega (alpha n) := by
      have h_spec := Nat.find_spec (F_omega_exists n)
      have h_eq :
          alpha n =
            @Nat.find (P_omega n) (P_omega_decidable n) (F_omega_exists n) := by
        unfold alpha
        rfl
      rw [h_eq]
      exact h_spec
    rw [h0] at h_spec
    rw [F_omega_zero] at h_spec
    omega
  omega

theorem target_bound_mono_const {C D m len : ℕ}
    (hCD : C ≤ D)
    (h : len ≤ C * (m + 1) * (alpha (m + 1) + 1)) :
    len ≤ D * (m + 1) * (alpha (m + 1) + 1) := by
  exact le_trans h (by
    gcongr)

end AckermannFacts

/-! ## Ported: the gammaOf engine defs (subset of CodexDS.CorrectedM7Shell) -/

section GammaEngineDefs

def MonotoneNat (beta : ℕ → ℕ) : Prop :=
  ∀ ⦃x y : ℕ⦄, x ≤ y → beta x ≤ beta y

def DecreasesAbove (threshold : ℕ) (f : ℕ → ℕ) : Prop :=
  ∀ n, threshold < n → f n < n

/-- Number of iterations of `f` needed to reach `threshold`. -/
def gammaOf (f : ℕ → ℕ) (threshold : ℕ)
    (hdec : DecreasesAbove threshold f) : ℕ → ℕ
  | n =>
      if h : n ≤ threshold then
        0
      else
        1 + gammaOf f threshold hdec (f n)
termination_by n => n
decreasing_by
  simp_wf
  exact hdec n (by omega)

theorem gammaOf_le {f : ℕ → ℕ} {threshold n : ℕ}
    {hdec : DecreasesAbove threshold f} (h : n ≤ threshold) :
    gammaOf f threshold hdec n = 0 := by
  rw [gammaOf]
  simp [h]

theorem gammaOf_gt {f : ℕ → ℕ} {threshold n : ℕ}
    {hdec : DecreasesAbove threshold f} (h : threshold < n) :
    gammaOf f threshold hdec n =
      1 + gammaOf f threshold hdec (f n) := by
  rw [gammaOf]
  simp [show ¬ n ≤ threshold by omega]

def Blocking_gamma_mono : Prop :=
  ∀ (f : ℕ → ℕ) (threshold : ℕ) (hdec : DecreasesAbove threshold f),
    MonotoneNat f →
    MonotoneNat (gammaOf f threshold hdec)

def Blocking_gamma_poly_alpha : Prop :=
  ∀ (beta : ℕ → ℕ) (c d threshold : ℕ)
    (hdec : DecreasesAbove threshold (fun z => beta (beta z))),
    MonotoneNat beta →
    (∀ z, beta z ≤ c * (alpha (z + 1) + 1) ^ d) →
    ∃ c' : ℕ, ∀ n,
      gammaOf (fun z => beta (beta z)) threshold hdec n
        ≤ c' * (alpha (n + 1) + 1)

end GammaEngineDefs

/-! ## Ported: gammaOf monotonicity + poly-alpha collapse (CodexDS.GammaBlockersClosed) -/

section GammaBlockersClosed

/-- The iterate count never exceeds its starting point: every counted step
strictly decreases the argument. -/
theorem gammaOf_le_self (f : ℕ → ℕ) (threshold : ℕ)
    (hdec : DecreasesAbove threshold f) :
    ∀ n, gammaOf f threshold hdec n ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n ≤ threshold
    · rw [gammaOf_le h]
      exact Nat.zero_le n
    · have hn : threshold < n := by omega
      have hlt : f n < n := hdec n hn
      have hrec := ih (f n) hlt
      rw [gammaOf_gt hn]
      omega

/-- **First T2 blocker, closed**: monotone `f` gives a monotone iterate
count. -/
theorem gamma_mono_proved : Blocking_gamma_mono := by
  intro f threshold hdec hf
  have main : ∀ y x, x ≤ y →
      gammaOf f threshold hdec x ≤ gammaOf f threshold hdec y := by
    intro y
    induction y using Nat.strong_induction_on with
    | _ y ih =>
      intro x hxy
      by_cases hy : y ≤ threshold
      · rw [gammaOf_le (le_trans hxy hy), gammaOf_le hy]
      · have hy' : threshold < y := by omega
        by_cases hx : x ≤ threshold
        · rw [gammaOf_le hx]
          exact Nat.zero_le _
        · have hx' : threshold < x := by omega
          rw [gammaOf_gt hx', gammaOf_gt hy']
          have hrec := ih (f y) (hdec y hy') (f x) (hf hxy)
          omega
  intro x y hxy
  exact main y x hxy

/-- `F 2` is exactly the powers of two. -/
theorem F_two_eq : ∀ n, F 2 n = 2 ^ n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      have h1 : F 2 (n + 1) = (F 1 ·)^[n + 1] 1 :=
        AckermannFacts.F_succ_succ 0 (n + 1)
      have h2 : (F 1 ·)^[n] 1 = F 2 n := (AckermannFacts.F_succ_succ 0 n).symm
      rw [h1, Function.iterate_succ_apply', h2, ih, AckermannFacts.F_one]
      ring

/-- One-step recurrence of the tower function `F 3`. -/
theorem F_three_succ (n : ℕ) : F 3 (n + 1) = 2 ^ F 3 n := by
  have h1 : F 3 (n + 1) = (F 2 ·)^[n + 1] 1 :=
    AckermannFacts.F_succ_succ 1 (n + 1)
  have h2 : (F 2 ·)^[n] 1 = F 3 n := (AckermannFacts.F_succ_succ 1 n).symm
  rw [h1, Function.iterate_succ_apply', h2, F_two_eq]

/-- The tower dominates the plain powers of two. -/
theorem two_pow_le_F_three {x : ℕ} (hx : 1 ≤ x) : 2 ^ x ≤ F 3 x := by
  have h := AckermannFacts.F_mono_left (j := 2) (k := 3) (by omega) (by omega)
    x hx
  rw [F_two_eq] at h
  exact h

/-- Every natural is below its own power of two. -/
theorem le_two_pow_self : ∀ n : ℕ, n ≤ 2 ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hpos : 0 < 2 ^ n := pow_pos (by omega) n
      have h2 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
        rw [pow_succ]
        ring
      omega

/-- Squares are below the powers of two from `4` on. -/
theorem sq_le_two_pow : ∀ x : ℕ, 4 ≤ x → x * x ≤ 2 ^ x := by
  intro x
  induction x with
  | zero => intro h; omega
  | succ x ih =>
      intro hx
      by_cases h4 : 4 ≤ x
      · have hrec : x * x ≤ 2 ^ x := ih h4
        have h4x : 4 * x ≤ x * x := Nat.mul_le_mul h4 (le_refl x)
        have hkey : (x + 1) * (x + 1) ≤ 2 * (x * x) := by linarith
        have hdbl : 2 * (x * x) ≤ 2 * 2 ^ x := Nat.mul_le_mul (le_refl 2) hrec
        have h2 : 2 ^ (x + 1) = 2 * 2 ^ x := by
          rw [pow_succ]
          ring
        linarith
      · have hx3 : x = 3 := by omega
        subst hx3
        norm_num

/-- A monotone `beta` whose double application decreases above `threshold` is
itself non-increasing above `threshold`. -/
theorem beta_le_self_of_double_dec {beta : ℕ → ℕ} {threshold : ℕ}
    (hmono : MonotoneNat beta)
    (hdec : DecreasesAbove threshold (fun z => beta (beta z)))
    {z : ℕ} (hz : threshold < z) :
    beta z ≤ z := by
  by_contra hgt
  push_neg at hgt
  have h1 : beta z ≤ beta (beta z) := hmono (Nat.le_of_lt hgt)
  have h2 : beta (beta z) < z := hdec z hz
  omega

/-- **The poly-to-alpha collapse kernel**: one double application of a
poly-alpha-bounded monotone `beta` drops `alpha (· + 1)` by at least one,
as soon as `alpha (z + 1)` clears the explicit constant `c + 4 * d + 7`. -/
theorem alpha_drop_step {beta : ℕ → ℕ} {c d threshold : ℕ}
    (hmono : MonotoneNat beta)
    (hdec : DecreasesAbove threshold (fun z => beta (beta z)))
    (hpoly : ∀ z, beta z ≤ c * (alpha (z + 1) + 1) ^ d)
    {z : ℕ} (hz : threshold < z) (ha : c + 4 * d + 7 ≤ alpha (z + 1)) :
    alpha (beta (beta z) + 1) + 1 ≤ alpha (z + 1) := by
  obtain ⟨x, hx⟩ : ∃ x, alpha (z + 1) = x + 2 := ⟨alpha (z + 1) - 2, by omega⟩
  have hx5 : c + 4 * d + 5 ≤ x := by omega
  -- the double-step image is polynomial in `a = alpha (z + 1)`, exponent `d`
  have hbz : beta z ≤ z := beta_le_self_of_double_dec hmono hdec hz
  have hinner : alpha (beta z + 1) ≤ alpha (z + 1) :=
    AckermannFacts.alpha_mono (by omega)
  have hgz : beta (beta z) ≤ c * (alpha (z + 1) + 1) ^ d := by
    have h1 : beta (beta z) ≤ c * (alpha (beta z + 1) + 1) ^ d := hpoly (beta z)
    have h2 : (alpha (beta z + 1) + 1) ^ d ≤ (alpha (z + 1) + 1) ^ d :=
      Nat.pow_le_pow_left (by omega) d
    have h3 : c * (alpha (beta z + 1) + 1) ^ d
        ≤ c * (alpha (z + 1) + 1) ^ d := Nat.mul_le_mul (le_refl c) h2
    exact le_trans h1 h3
  -- poly(a) + 1 ≤ 2 ^ (linear in a)
  have hpoly2 : c * (alpha (z + 1) + 1) ^ d + 1
      ≤ 2 ^ (c + (alpha (z + 1) + 1) * d + 1) := by
    have hc : c ≤ 2 ^ c := le_two_pow_self c
    have hbase : alpha (z + 1) + 1 ≤ 2 ^ (alpha (z + 1) + 1) :=
      le_two_pow_self (alpha (z + 1) + 1)
    have hpow : (alpha (z + 1) + 1) ^ d ≤ 2 ^ ((alpha (z + 1) + 1) * d) := by
      have h1 : (alpha (z + 1) + 1) ^ d ≤ (2 ^ (alpha (z + 1) + 1)) ^ d :=
        Nat.pow_le_pow_left hbase d
      have h2 : (2 ^ (alpha (z + 1) + 1)) ^ d
          = 2 ^ ((alpha (z + 1) + 1) * d) :=
        (pow_mul 2 (alpha (z + 1) + 1) d).symm
      rw [h2] at h1
      exact h1
    have hmul : c * (alpha (z + 1) + 1) ^ d
        ≤ 2 ^ c * 2 ^ ((alpha (z + 1) + 1) * d) := Nat.mul_le_mul hc hpow
    have hadd : 2 ^ c * 2 ^ ((alpha (z + 1) + 1) * d)
        = 2 ^ (c + (alpha (z + 1) + 1) * d) :=
      (pow_add 2 c ((alpha (z + 1) + 1) * d)).symm
    have hpos : 0 < 2 ^ (c + (alpha (z + 1) + 1) * d) := pow_pos (by omega) _
    have hdbl : 2 ^ (c + (alpha (z + 1) + 1) * d + 1)
        = 2 ^ (c + (alpha (z + 1) + 1) * d) * 2 :=
      pow_succ 2 (c + (alpha (z + 1) + 1) * d)
    linarith
  -- the linear exponent fits under the square at `x = a - 2`
  have hlin : c + (alpha (z + 1) + 1) * d + 1 ≤ x * x := by
    have hx1 : 1 ≤ x := by omega
    have h1 : (c + 4 * d + 5) * x ≤ x * x := Nat.mul_le_mul hx5 (le_refl x)
    have e1 : c ≤ c * x := Nat.le_mul_of_pos_right c (by omega)
    have e2 : 3 * d ≤ 3 * d * x := Nat.le_mul_of_pos_right (3 * d) (by omega)
    have ha1 : alpha (z + 1) + 1 = x + 3 := by omega
    rw [ha1]
    nlinarith [h1, e1, e2, hx1]
  -- assemble through the tower: x * x ≤ 2 ^ x ≤ F 3 x
  have hsq : x * x ≤ 2 ^ x := sq_le_two_pow x (by omega)
  have hF3 : 2 ^ x ≤ F 3 x := two_pow_le_F_three (by omega)
  have hexp : c + (alpha (z + 1) + 1) * d + 1 ≤ F 3 x :=
    le_trans hlin (le_trans hsq hF3)
  have hmono2 : 2 ^ (c + (alpha (z + 1) + 1) * d + 1) ≤ 2 ^ F 3 x :=
    Nat.pow_le_pow_right (by omega) hexp
  have htower : 2 ^ F 3 x = F 3 (x + 1) := (F_three_succ x).symm
  have homega : F 3 (x + 1) ≤ F_omega (x + 1) := by
    rw [F_omega]
    exact AckermannFacts.F_mono_left (by omega) (by omega) (x + 1) (by omega)
  have homega' : 2 ^ F 3 x ≤ F_omega (x + 1) := by
    rw [htower]
    exact homega
  -- conclude through the alpha interface
  have hfinal : beta (beta z) + 1 ≤ F_omega (x + 1) := by
    have s1 : beta (beta z) + 1 ≤ c * (alpha (z + 1) + 1) ^ d + 1 :=
      Nat.add_le_add_right hgz 1
    exact le_trans s1 (le_trans hpoly2 (le_trans hmono2 homega'))
  have hcollapse : alpha (beta (beta z) + 1) ≤ x + 1 :=
    (AckermannFacts.alpha_le_iff (beta (beta z) + 1) (x + 1)).mpr hfinal
  omega

/-- **Second T2 blocker, closed**: iterating the double application of a
monotone poly-alpha-bounded `beta` down to any fixed threshold takes at most
`(F_omega (c + 4 * d + 7) + 1) * (alpha (n + 1) + 1)` steps. -/
theorem gamma_poly_alpha_proved : Blocking_gamma_poly_alpha := by
  intro beta c d threshold hdec hmono hpoly
  refine ⟨F_omega (c + 4 * d + 7) + 1, ?_⟩
  have main : ∀ k z, alpha (z + 1) ≤ c + 4 * d + 7 + k →
      gammaOf (fun z => beta (beta z)) threshold hdec z
        ≤ F_omega (c + 4 * d + 7) + k := by
    intro k
    induction k with
    | zero =>
        intro z hz
        have hzF : z + 1 ≤ F_omega (c + 4 * d + 7) :=
          (AckermannFacts.alpha_le_iff (z + 1) (c + 4 * d + 7)).mp (by omega)
        have hself := gammaOf_le_self (fun z => beta (beta z)) threshold hdec z
        omega
    | succ k ih =>
        intro z hz
        by_cases hsmall : alpha (z + 1) ≤ c + 4 * d + 7 + k
        · have := ih z hsmall
          omega
        · by_cases hth : z ≤ threshold
          · rw [gammaOf_le hth]
            omega
          · have hth' : threshold < z := by omega
            have heq : gammaOf (fun z => beta (beta z)) threshold hdec z
                = 1 + gammaOf (fun z => beta (beta z)) threshold hdec
                    (beta (beta z)) := gammaOf_gt hth'
            have hdrop : alpha (beta (beta z) + 1) + 1 ≤ alpha (z + 1) :=
              alpha_drop_step hmono hdec hpoly hth' (by omega)
            have hnext := ih (beta (beta z)) (by omega)
            omega
  intro n
  have h := main (alpha (n + 1)) n (by omega)
  have e1 : F_omega (c + 4 * d + 7)
      ≤ F_omega (c + 4 * d + 7) * (alpha (n + 1) + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have e2 : (F_omega (c + 4 * d + 7) + 1) * (alpha (n + 1) + 1)
      = F_omega (c + 4 * d + 7) * (alpha (n + 1) + 1) + (alpha (n + 1) + 1) := by
    ring
  linarith

end GammaBlockersClosed

/-! ## Ported: the abstract recurrence-telescoping backbone (CodexDS.RecurrenceTelescope) -/

section RecurrenceTelescope

/-- The two hypotheses packaging an aggregated-per-level recurrence for a cost
function `T` with descent schedule `f`, flat per-level slope `c`, and base
slope `c0`. -/
def RecBase (T : ℕ → ℕ) (threshold c0 : ℕ) : Prop :=
  ∀ m, m ≤ threshold → T m ≤ c0 * m

def RecStep (T f : ℕ → ℕ) (threshold c : ℕ) : Prop :=
  ∀ m, threshold < m → T m ≤ T (f m) + c * m

/-- **Level-unfolding lemma (deliverable 1).**  An aggregated-per-level
recurrence telescopes to `c · n · L + c0 · n`, where `L` is the descent depth
`gammaOf f threshold hdec n`.  Proof: strong induction on the size.  Above the
threshold one descent level peels a flat `c * m ≤ c * n` charge and `gammaOf`
increments by one; `f m ≤ m` (from `DecreasesAbove`) keeps the recursive
estimate's size factor below `m`. -/
theorem recursion_unfold
    (T f : ℕ → ℕ) (threshold c c0 : ℕ)
    (hdec : DecreasesAbove threshold f)
    (hbase : RecBase T threshold c0)
    (hstep : RecStep T f threshold c) :
    ∀ n, T n ≤ c * n * gammaOf f threshold hdec n + c0 * n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n ≤ threshold
    · -- base case: the descent depth is zero, the base charge suffices
      rw [gammaOf_le (hdec := hdec) h]
      have hb := hbase n h
      simpa using hb
    · have hn : threshold < n := by omega
      have hfn : f n < n := hdec n hn
      have hflen : f n ≤ n := Nat.le_of_lt hfn
      -- one descent level: gammaOf increments, flat charge is `c * n`
      have hrec := ih (f n) hfn
      have hstepn := hstep n hn
      have heq : gammaOf f threshold hdec n
          = 1 + gammaOf f threshold hdec (f n) := gammaOf_gt hn
      -- size monotonicity of the two estimate factors
      have hmulA : c * (f n) * gammaOf f threshold hdec (f n)
          ≤ c * n * gammaOf f threshold hdec (f n) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left c hflen)
      have hmulB : c0 * (f n) ≤ c0 * n := Nat.mul_le_mul_left c0 hflen
      -- assemble: T n ≤ T(f n) + c*n
      --                ≤ (c*(f n)*G + c0*(f n)) + c*n
      --                ≤ c*n*G + c0*n + c*n = c*n*(G+1) + c0*n
      have hTfn : T (f n) ≤ c * n * gammaOf f threshold hdec (f n) + c0 * n :=
        le_trans hrec (by omega)
      have hexpand : c * n * gammaOf f threshold hdec n
          = c * n * gammaOf f threshold hdec (f n) + c * n := by
        rw [heq]; ring
      calc T n ≤ T (f n) + c * n := hstepn
        _ ≤ (c * n * gammaOf f threshold hdec (f n) + c0 * n) + c * n := by
              omega
        _ = c * n * gammaOf f threshold hdec n + c0 * n := by
              rw [hexpand]; ring

/-! ### Deliverable 2: the alpha collapse of the descent depth

For the *double schedule* `f = fun z => beta (beta z)` with `beta` monotone and
polynomially `alpha`-bounded, `gamma_poly_alpha_proved` gives a constant `c'`
with `gammaOf f threshold hdec n ≤ c' * (alpha (n+1) + 1)`.  We package this as
a standalone level-count bound. -/

theorem recursion_depth_alpha
    (beta : ℕ → ℕ) (c d threshold : ℕ)
    (hdec : DecreasesAbove threshold (fun z => beta (beta z)))
    (hmono : MonotoneNat beta)
    (hpoly : ∀ z, beta z ≤ c * (alpha (z + 1) + 1) ^ d) :
    ∃ c' : ℕ, ∀ n,
      gammaOf (fun z => beta (beta z)) threshold hdec n
        ≤ c' * (alpha (n + 1) + 1) :=
  gamma_poly_alpha_proved beta c d threshold hdec hmono hpoly

/-! ### Deliverable 3: the combined closed form `T n ≤ C·n·alpha(n+1) + C'·n`

Composing the level-unfolding (deliverable 1) with the depth collapse
(deliverable 2) gives the closed `n · alpha` bound.  The explicit constants are
`C = c * c'` and `C' = c * c' + c0`, where `c'` is the depth constant from
`gamma_poly_alpha_proved` (itself `F_omega (c_beta + 4 d + 7) + 1`). -/

theorem recursion_telescope
    (T beta : ℕ → ℕ) (cβ d threshold c c0 : ℕ)
    (hdec : DecreasesAbove threshold (fun z => beta (beta z)))
    (hmono : MonotoneNat beta)
    (hpoly : ∀ z, beta z ≤ cβ * (alpha (z + 1) + 1) ^ d)
    (hbase : RecBase T threshold c0)
    (hstep : RecStep T (fun z => beta (beta z)) threshold c) :
    ∃ C C' : ℕ, ∀ n,
      T n ≤ C * (n * alpha (n + 1)) + C' * n := by
  -- depth collapse
  obtain ⟨c', hc'⟩ := recursion_depth_alpha beta cβ d threshold hdec hmono hpoly
  -- level unfolding
  have hunfold := recursion_unfold T (fun z => beta (beta z)) threshold c c0
    hdec hbase hstep
  refine ⟨c * c', c * c' + c0, ?_⟩
  intro n
  -- substitute the depth bound into the unfolded estimate
  have h1 : T n
      ≤ c * n * gammaOf (fun z => beta (beta z)) threshold hdec n + c0 * n :=
    hunfold n
  have hG : gammaOf (fun z => beta (beta z)) threshold hdec n
      ≤ c' * (alpha (n + 1) + 1) := hc' n
  have h2 : c * n * gammaOf (fun z => beta (beta z)) threshold hdec n
      ≤ c * n * (c' * (alpha (n + 1) + 1)) :=
    Nat.mul_le_mul_left (c * n) hG
  -- expand `c * n * (c' * (alpha+1)) = (c*c')*(n*alpha) + (c*c')*n`
  have hexpand : c * n * (c' * (alpha (n + 1) + 1))
      = (c * c') * (n * alpha (n + 1)) + (c * c') * n := by ring
  have hfold : (c * c') * (n * alpha (n + 1)) + (c * c') * n + c0 * n
      = (c * c') * (n * alpha (n + 1)) + (c * c' + c0) * n := by ring
  -- assemble through the explicit `ring` rewrites and `omega`
  calc T n
      ≤ c * n * gammaOf (fun z => beta (beta z)) threshold hdec n + c0 * n := h1
    _ ≤ c * n * (c' * (alpha (n + 1) + 1)) + c0 * n :=
          Nat.add_le_add_right h2 (c0 * n)
    _ = (c * c') * (n * alpha (n + 1)) + (c * c' + c0) * n := by
          rw [hexpand]; ring

end RecurrenceTelescope

/-! ## §GLUE.1 The `alpha (n+1) → alpha n` reconciliation

(`gamma_mono_proved` and `gamma_poly_alpha_proved` are already ported verbatim
above in the `GammaBlockersClosed` block.)

`turn_main`'s `RecursionTelescopedBound` uses `alpha n`, while the codex
telescope produces `alpha (n + 1)`.  Since `alpha` increases by at most one per
step, `n · alpha (n+1) ≤ n · alpha n + n`, folding the extra `n` into the linear
term.  We prove `alpha (n+1) ≤ alpha n + 1` from the ported Ackermann interface. -/

open AckermannFacts in
/-- `F_omega` jumps by at least one at each step: `F_omega m + 1 ≤ F_omega (m+1)`.
For `m = 0`, `F_omega 1 = 2`.  For `m ≥ 1`, `F (m+1)` is strictly increasing
(`F (m+1) (m+1) > F (m+1) m ≥ F m m = F_omega m`). -/
theorem F_omega_step_ge (m : ℕ) : F_omega m + 1 ≤ F_omega (m + 1) := by
  cases m with
  | zero =>
    -- F_omega 0 = 0, F_omega 1 = F 1 1 = 2
    have h0 : F_omega 0 = 0 := F_omega_zero
    have h1 : F_omega 1 = 2 := by
      rw [F_omega]; exact F_k_1_eq_2 (by omega)
    rw [h0, h1]; omega
  | succ k =>
    -- m = k+1 ≥ 1.  F_omega m = F m m ≤ F (m+1) m < F (m+1) (m+1) = F_omega (m+1),
    -- with F (m+1)(m+1) = F m (F (m+1) m) via the iterate recurrence.
    have hm : 1 ≤ k + 1 := by omega
    have h1 : F (k + 1) (k + 1) ≤ F (k + 2) (k + 1) :=
      F_mono_left hm (by omega) (k + 1) hm
    have hval1 : 1 ≤ F (k + 2) (k + 1) := F_iterate_ge_one (by omega) hm
    -- F (k+2)(k+2) = (F (k+1)·)^[k+2] 1 = F (k+1) ((F (k+1)·)^[k+1] 1)
    --             = F (k+1) (F (k+2)(k+1))
    have hexp1 : F (k + 2) (k + 2) = (F (k + 1) ·)^[k + 2] 1 := F_succ_succ k (k + 2)
    have hexp2 : F (k + 2) (k + 1) = (F (k + 1) ·)^[k + 1] 1 := F_succ_succ k (k + 1)
    have hstep : F (k + 2) (k + 2) = F (k + 1) (F (k + 2) (k + 1)) := by
      rw [hexp1, hexp2, Function.iterate_succ_apply']
    have hinfl : F (k + 2) (k + 1) < F (k + 1) (F (k + 2) (k + 1)) :=
      F_inflationary hm hval1
    -- F_omega (k+1) = F (k+1)(k+1),  F_omega (k+2) = F (k+2)(k+2)
    have e1 : F_omega (k + 1) = F (k + 1) (k + 1) := by rw [F_omega]
    have e2 : F_omega (k + 1 + 1) = F (k + 2) (k + 2) := by rw [F_omega]
    rw [e1, e2, hstep]
    omega

theorem alpha_step_le_one (n : ℕ) : alpha (n + 1) ≤ alpha n + 1 := by
  apply AckermannFacts.alpha_min (n := n + 1) (m := alpha n + 1)
  have hspec : n ≤ F_omega (alpha n) := AckermannFacts.alpha_spec n
  have hstep : F_omega (alpha n) + 1 ≤ F_omega (alpha n + 1) := F_omega_step_ge (alpha n)
  omega

/-! ## §GLUE.3 The abstract `RecursionTelescopedBound`-shape capstone

For an arbitrary size-indexed touched-sum `T : ℕ → ℕ`, the per-level-flat W-D
recurrence (`RecBase` + `RecStep` for the squaring schedule `fun z => beta (beta
z)`) telescopes to the exact `turn_main` conclusion shape `T n ≤ C·(n·alpha n) +
C'·n` (note: `alpha n`, NOT `alpha (n+1)`).  This is `recursion_telescope`
post-composed with the `alpha (n+1) ≤ alpha n + 1` reconciliation.

Instantiating `T n := ∑ i ∈ Finset.range n, tpLenN init X i`, `beta` = the
`B = β²` block-size schedule, and supplying the concrete W-D `RecStep`
(`wdRecurrenceStep_proved` iterated, i.e. residual-conditional) discharges
`RecursionTelescopedBound` verbatim inside `turn_main`. -/
theorem recursionTelescopedBound_abstract
    (T beta : ℕ → ℕ) (cβ d threshold c c0 : ℕ)
    (hdec : DecreasesAbove threshold (fun z => beta (beta z)))
    (hmono : MonotoneNat beta)
    (hpoly : ∀ z, beta z ≤ cβ * (alpha (z + 1) + 1) ^ d)
    (hbase : RecBase T threshold c0)
    (hstep : RecStep T (fun z => beta (beta z)) threshold c) :
    ∃ C C' : ℕ, ∀ n,
      T n ≤ C * (n * alpha n) + C' * n := by
  obtain ⟨C, C', hCC⟩ :=
    recursion_telescope T beta cβ d threshold c c0 hdec hmono hpoly hbase hstep
  -- reconcile alpha (n+1) with alpha n via the one-step bound
  refine ⟨C, C' + C, ?_⟩
  intro n
  have h := hCC n
  -- n * alpha (n+1) ≤ n * (alpha n + 1) = n * alpha n + n
  have hαstep : alpha (n + 1) ≤ alpha n + 1 := alpha_step_le_one n
  have hmul : n * alpha (n + 1) ≤ n * (alpha n + 1) :=
    Nat.mul_le_mul_left n hαstep
  have hexp : n * (alpha n + 1) = n * alpha n + n := by ring
  calc T n ≤ C * (n * alpha (n + 1)) + C' * n := h
    _ ≤ C * (n * alpha n + n) + C' * n := by
        apply Nat.add_le_add_right
        apply Nat.mul_le_mul_left
        rw [hexp] at hmul; exact hmul
    _ = C * (n * alpha n) + (C' + C) * n := by ring

end GlueTelescope

#print axioms GlueTelescope.gammaOf_le
#print axioms GlueTelescope.gammaOf_gt
#print axioms GlueTelescope.gammaOf_le_self
#print axioms GlueTelescope.gamma_mono_proved
#print axioms GlueTelescope.gamma_poly_alpha_proved
#print axioms GlueTelescope.recursion_unfold
#print axioms GlueTelescope.recursion_depth_alpha
#print axioms GlueTelescope.recursion_telescope
#print axioms GlueTelescope.F_omega_step_ge
#print axioms GlueTelescope.alpha_step_le_one
#print axioms GlueTelescope.recursionTelescopedBound_abstract
