module

public import Certificates.Kernel.Sporadic.OddCore.SuzRTF
public import Certificates.Kernel.Sporadic.L2.G4
public import CFSG.Sporadic.SuzRecog.LevelTwoCoverCheck
meta import CFSG.Sporadic.SuzRecog.LevelTwoCoverCheck
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.SuzRTV CFSG.Sporadic.SuzRecog.LevelTwoCoverData.voltStr

#kmisc_hexflat CertificateChecks.KernelSpor.SuzRTV CFSG.Sporadic.SuzRecog.LevelTwoCoverData.voltStr
  1 36 2 2835

namespace CertificateChecks.KernelSpor.SuzRTH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.Sporadic.SuzRecog.RootTwistCheck CFSG.Sporadic.SuzRecog.LevelTwoCover
open CFSG.Sporadic.SuzRecog.LevelTwoCoverData CFSG.Sporadic.SuzRecog.ElimCert
open CFSG.Sporadic.SuzRecog.LevelTwo (nbr posIn p1)
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.L2K

@[expose] noncomputable def voltK (x k : Nat) : Nat := pg 2 (mask 2) (SuzRTV.F x) k

@[expose] noncomputable def cP1 (i k : Nat) : Nat := nbK 342 k + 2997 * ((i + voltK 342 k) % 3)

@[expose] noncomputable def holK : Bool :=
  Nat.beq (nbK 0 34) 2970 && allN 34 (fun k => !Nat.beq (nbK 0 k) 2970) &&
    Nat.beq (nbK 0 23) 2890 && allN 23 (fun k => !Nat.beq (nbK 0 k) 2890) &&
    Nat.beq (voltK 0 34 % 3) 2 && Nat.beq (voltK 0 23 % 3) 0 &&
    allN 36 (fun k => !Nat.beq (cP1 0 k) 8964) && allN 36 (fun k => !Nat.beq (cP1 1 k) 8964) &&
    Nat.beq (cP1 2 19) 8964 && allN 36 (fun k => !Nat.beq (cP1 0 k) 2890) &&
    Nat.beq (cP1 1 22) 2890

theorem kHol : holK = true := by quickRfl

theorem neg_hol : Bool.not (Nat.beq (cP1 0 22) 2890) = true := by quickRfl

theorem volt_get {x k : Nat} (hx : x < 2835) (hk : k < 36) : volt[36 * x + k]! = voltK x k := by
  unfold volt
  rw [L2G.hexTable_at (by omega), Nat.zero_add]
  exact L2G.hexE SuzRTV.eq SuzRTV.all hx hk

theorem nbrC_get {u : Nat} (hu : u < 8991) : nbrC[u]! = coverList nbr volt u := by
  unfold nbrC coverLists
  rw [getElem!_pos _ u (by rw [Array.size_ofFn]; exact hu), Array.getElem_ofFn]

theorem nbrC_low {u : Nat} (hu : u < 8991) (hl : u % 2997 < 2835) {k : Nat} (hk : k < 36) :
    (nbrC[u]!)[k]! = nbK (u % 2997) k + 2997 * ((u / 2997 + voltK (u % 2997) k) % 3) := by
  rw [nbrC_get hu]
  unfold coverList
  simp only [hl, ↓reduceIte]
  rw [getElem!_pos _ k (by rw [Array.size_ofFn]; exact hk), Array.getElem_ofFn]
  dsimp only
  rw [L2G.nbr_get hl hk, volt_get hl hk]

theorem nbrC_size {u : Nat} (hu : u < 8991) (hl : u % 2997 < 2835) : (nbrC[u]!).size = 36 := by
  rw [nbrC_get hu]
  unfold coverList
  simp only [hl, ↓reduceIte, Array.size_ofFn]

theorem nbrC_high {u : Nat} (hu : u < 8991) (hl : 2835 ≤ u % 2997) : nbrC[u]! = #[] := by
  rw [nbrC_get hu]
  unfold coverList
  have hl' : ¬ u % 2997 < 2835 := by omega
  simp only [hl', ↓reduceIte]

theorem occB_nil (y : Nat) : occB #[] y = false := by
  simp [occB]

theorem occB_true {s : Array Nat} {y k : Nat} (hk : k < s.size) (h : s[k]! = y) :
    occB s y = true := by
  unfold occB
  rw [List.any_eq_true]
  exact ⟨k, List.mem_range.2 hk, by rw [h]; exact beq_self_eq_true y⟩

theorem occB_false {s : Array Nat} {y : Nat} (h : ∀ k < s.size, s[k]! ≠ y) : occB s y = false := by
  unfold occB
  rw [List.any_eq_false]
  intro k hk e
  exact h k (List.mem_range.1 hk) (beq_iff_eq.1 e)

theorem parts : nbK 0 34 = 2970 ∧ (∀ k < 34, nbK 0 k ≠ 2970) ∧ nbK 0 23 = 2890 ∧
    (∀ k < 23, nbK 0 k ≠ 2890) ∧ voltK 0 34 % 3 = 2 ∧ voltK 0 23 % 3 = 0 ∧
    (∀ k < 36, cP1 0 k ≠ 8964) ∧ (∀ k < 36, cP1 1 k ≠ 8964) ∧ cP1 2 19 = 8964 ∧
    (∀ k < 36, cP1 0 k ≠ 2890) ∧ cP1 1 22 = 2890 := by
  have h := kHol
  unfold holK at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  rw [L2G.nbeq] at h1 h3 h5 h6 h9 h11
  have ne : ∀ {n : Nat} {f : Nat → Nat} {y : Nat}, allN n (fun k => !Nat.beq (f k) y) = true →
      ∀ k < n, f k ≠ y := by
    intro n f y hh k hk e
    have := allN_spec hh k hk
    rw [e, Nat.beq_refl] at this
    exact Bool.false_ne_true this
  exact ⟨h1, ne h2, h3, ne h4, h5, h6, ne h7, ne h8, h9, ne h10, h11⟩

attribute [local irreducible] nbr in
theorem posIn_eq {y k : Nat} (hk : k < 36) (h1 : nbK 0 k = y) (h2 : ∀ j < k, nbK 0 j ≠ y) :
    posIn 0 y = k := by
  unfold posIn
  have hs := L2G.nbr_size (x := 0) (by norm_num)
  have g : ∀ j (hj : j < (nbr[0]!).size), (nbr[0]!)[j] = nbK 0 j := fun j hj => by
    have hj' : j < 36 := by
      rw [hs] at hj
      exact hj
    rw [← getElem!_pos _ j hj, L2G.nbr_get (by norm_num) hj']
  have hk' : k < (nbr[0]!).size := by
    rw [hs]
    exact hk
  rw [Array.findIdx?_eq_some_iff_getElem.2 ⟨hk', by rw [g, h1]; exact beq_self_eq_true y,
    fun j hj => by rw [g, beq_iff_eq]; exact h2 j hj⟩]
  rfl

theorem pos0 : posIn 0 2970 = 34 := posIn_eq (by norm_num) parts.1 parts.2.1

theorem pos1 : posIn 0 2890 = 23 := posIn_eq (by norm_num) parts.2.2.1 parts.2.2.2.1

theorem lift0 : liftAt0 2970 = 8964 := by
  unfold liftAt0
  rw [pos0, nbrC_low (by norm_num) (by norm_num) (by norm_num)]
  simp only [Nat.zero_mod, Nat.zero_div, Nat.zero_add]
  rw [parts.1, parts.2.2.2.2.1]

theorem lift1 : liftAt0 2890 = 2890 := by
  unfold liftAt0
  rw [pos1, nbrC_low (by norm_num) (by norm_num) (by norm_num)]
  simp only [Nat.zero_mod, Nat.zero_div, Nat.zero_add]
  rw [parts.2.2.1, parts.2.2.2.2.2.1]

theorem listed0 : listedAt0 2970 = true := by
  unfold listedAt0
  rw [pos0, L2G.nbr_get (by norm_num) (by norm_num), parts.1]
  rfl

theorem listed1 : listedAt0 2890 = true := by
  unfold listedAt0
  rw [pos1, L2G.nbr_get (by norm_num) (by norm_num), parts.2.2.1]
  rfl

theorem adj_eq {i u : Nat} (hu : u < 8991) (hl : 2835 ≤ u % 2997) (hne : 342 + 2997 * i ≠ u) :
    adjB nbrC (342 + 2997 * i) u = occB nbrC[342 + 2997 * i]! u := by
  unfold adjB
  rw [nbrC_high hu hl, occB_nil, Bool.or_false]
  simp [hne]

theorem cP1_get {i k : Nat} (hi : i < 3) (hk : k < 36) :
    (nbrC[342 + 2997 * i]!)[k]! = cP1 i k := by
  rw [nbrC_low (by omega) (by omega) hk]
  have e1 : (342 + 2997 * i) % 2997 = 342 := by omega
  have e2 : (342 + 2997 * i) / 2997 = i := by omega
  rw [e1, e2]
  rfl

theorem occ_true {i u k : Nat} (hi : i < 3) (hk : k < 36) (h : cP1 i k = u) :
    occB nbrC[342 + 2997 * i]! u = true :=
  occB_true (by rw [nbrC_size (by omega) (by omega)]; exact hk) (by rw [cP1_get hi hk, h])

theorem occ_false {i u : Nat} (hi : i < 3) (h : ∀ k < 36, cP1 i k ≠ u) :
    occB nbrC[342 + 2997 * i]! u = false :=
  occB_false fun k hk => by
    rw [nbrC_size (by omega) (by omega)] at hk
    rw [cP1_get hi hk]
    exact h k hk

theorem range3 : List.range 3 = [0, 1, 2] := rfl

theorem sheet0 : sheetAt 8964 = 2 := by
  unfold sheetAt
  rw [L2G.p1_eq, range3]
  have a0 := adj_eq (i := 0) (u := 8964) (by norm_num) (by norm_num) (by norm_num)
  have a1 := adj_eq (i := 1) (u := 8964) (by norm_num) (by norm_num) (by norm_num)
  have a2 := adj_eq (i := 2) (u := 8964) (by norm_num) (by norm_num) (by norm_num)
  rw [occ_false (by norm_num) parts.2.2.2.2.2.2.1] at a0
  rw [occ_false (by norm_num) parts.2.2.2.2.2.2.2.1] at a1
  rw [occ_true (by norm_num) (by norm_num) parts.2.2.2.2.2.2.2.2.1] at a2
  simp [a0, a1, a2]

theorem sheet1 : sheetAt 2890 = 1 := by
  unfold sheetAt
  rw [L2G.p1_eq, range3]
  have a0 := adj_eq (i := 0) (u := 2890) (by norm_num) (by norm_num) (by norm_num)
  have a1 := adj_eq (i := 1) (u := 2890) (by norm_num) (by norm_num) (by norm_num)
  rw [occ_false (by norm_num) parts.2.2.2.2.2.2.2.2.2.1] at a0
  rw [occ_true (by norm_num) (by norm_num) parts.2.2.2.2.2.2.2.2.2.2] at a1
  simp [a0, a1]

theorem holOK_true : holOK = true := by
  have b0 : adjB nbrC (p1 + 2997 * 2) 8964 = true := by
    rw [L2G.p1_eq, adj_eq (by norm_num) (by norm_num) (by norm_num)]
    exact occ_true (by norm_num) (by norm_num) parts.2.2.2.2.2.2.2.2.1
  have b1 : adjB nbrC (p1 + 2997 * 1) 2890 = true := by
    rw [L2G.p1_eq, adj_eq (by norm_num) (by norm_num) (by norm_num)]
    exact occ_true (by norm_num) (by norm_num) parts.2.2.2.2.2.2.2.2.2.2
  unfold holOK sheetOK
  rw [lift0, lift1, sheet0, sheet1, listed0, listed1, b0, b1]
  rfl

end CertificateChecks.KernelSpor.SuzRTH

end
