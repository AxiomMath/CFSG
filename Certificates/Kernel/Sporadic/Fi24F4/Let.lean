module

public import Certificates.Kernel.Sporadic.Fi24K.C2077
public import CFSG.Certificates.Kernel.Spor.Fi24F4Sound
public import CFSG.Sporadic.Fi24I301.Letters

public section

namespace CertificateChecks.KernelSpor.Fi24F4

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.Fi24F4 CFSG.KS.Fi24F4
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.FischerOddCore
open CFSG.Sporadic.Fi24I301 CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi24C
open CFSG.KS.Raw.Orb (PRep)

theorem prep_of_rep {n w P : Nat} {g : Equiv.Perm (Fin n)} (h : Rep n (unpack n w P) g) :
    PRep n w P g := fun x => by
  rw [← CFSG.KS.Raw.Orb.unpack_get x.isLt]
  exact h x

theorem prep_gen {n w P PI : Nat} (h : permOK n w (mask w) (n * w) P PI = true) :
    PRep n w P (permOfArr n (unpack n w P)) ∧ PRep n w PI (permOfArr n (unpack n w P))⁻¹ := by
  have hi := (invEqK_sound (n := n) (w := w) (p := P) (r := PI) h).2
  obtain ⟨h1, h2⟩ := rep_permOfArr hi
  exact ⟨prep_of_rep h1, prep_of_rep h2⟩

theorem fi24Sa_eq : fi24Sa = permOfArr 504 (unpack 504 9 (Fi24KC.S 0)) := by
  rw [fi24Sa, kS, ofFn_get (by norm_num)]

theorem fi24Sb_eq : fi24Sb = permOfArr 504 (unpack 504 9 (Fi24KC.S 1)) := by
  rw [fi24Sb, kS, ofFn_get (by norm_num)]

theorem fi24Pa_eq : fi24Pa = permOfArr 378 (unpack 378 9 (Fi24PC.S 0)) := by
  rw [fi24Pa, pS, ofFn_get (by norm_num)]

theorem fi24Pb_eq : fi24Pb = permOfArr 378 (unpack 378 9 (Fi24PC.S 1)) := by
  rw [fi24Pb, pS, ofFn_get (by norm_num)]

theorem permK' {j : Nat} (hj : j < 12) :
    permOK 504 9 (mask 9) (504 * 9) (Fi24KC.S j) (Fi24KC.SI j) = true := allN_spec permK j hj

theorem permP' {j : Nat} (hj : j < 10) :
    permOK 378 9 (mask 9) (378 * 9) (Fi24PC.S j) (Fi24PC.SI j) = true := allN_spec permP j hj

@[expose] def okLet (z : ℤ) : Prop := z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2

theorem prep_kLet {z : ℤ} (hz : okLet z) :
    PRep 504 9 (letP Fi24KC.S Fi24KC.SI z) (kLet z) := by
  rcases hz with rfl | rfl | rfl | rfl
  · rw [show kLet 1 = fi24Sa by simp [kLet], fi24Sa_eq]
    exact (prep_gen (permK' (by norm_num : 0 < 12))).1
  · rw [show kLet (-1) = fi24Sa⁻¹ by simp [kLet], fi24Sa_eq]
    exact (prep_gen (permK' (by norm_num : 0 < 12))).2
  · rw [show kLet 2 = fi24Sb by simp [kLet], fi24Sb_eq]
    exact (prep_gen (permK' (by norm_num : 1 < 12))).1
  · rw [show kLet (-2) = fi24Sb⁻¹ by simp [kLet], fi24Sb_eq]
    exact (prep_gen (permK' (by norm_num : 1 < 12))).2

theorem prep_pLet {z : ℤ} (hz : okLet z) :
    PRep 378 9 (letP Fi24PC.S Fi24PC.SI z) (pLet z) := by
  rcases hz with rfl | rfl | rfl | rfl
  · rw [show pLet 1 = fi24Pa by simp [pLet], fi24Pa_eq]
    exact (prep_gen (permP' (by norm_num : 0 < 10))).1
  · rw [show pLet (-1) = fi24Pa⁻¹ by simp [pLet], fi24Pa_eq]
    exact (prep_gen (permP' (by norm_num : 0 < 10))).2
  · rw [show pLet 2 = fi24Pb by simp [pLet], fi24Pb_eq]
    exact (prep_gen (permP' (by norm_num : 1 < 10))).1
  · rw [show pLet (-2) = fi24Pb⁻¹ by simp [pLet], fi24Pb_eq]
    exact (prep_gen (permP' (by norm_num : 1 < 10))).2

theorem okLet_of {wd : List ℤ} (h : wd.all (fun z => z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) = true) :
    ∀ z ∈ wd, okLet z := fun z hz => by
  have := List.all_eq_true.1 h z hz
  simpa [okLet] using this

theorem prep_kWord {wd : List ℤ} {P : Nat}
    (hl : wd.all (fun z => z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) = true)
    (h : recOK 504 9 (mask 9) P Fi24KC.S Fi24KC.SI wd = true) :
    PRep 504 9 P (CFSG.Sporadic.Th.wordG kLet wd) ∧ canonK 504 9 (mask 9) (504 * 9) P = true :=
  prep_of_recOK (fun z hz => prep_kLet (okLet_of hl z hz)) h

theorem prep_pWord {wd : List ℤ} {P : Nat}
    (hl : wd.all (fun z => z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) = true)
    (h : recOK 378 9 (mask 9) P Fi24PC.S Fi24PC.SI wd = true) :
    PRep 378 9 P (CFSG.Sporadic.Th.wordG pLet wd) ∧ canonK 378 9 (mask 9) (378 * 9) P = true :=
  prep_of_recOK (fun z hz => prep_pLet (okLet_of hl z hz)) h

end CertificateChecks.KernelSpor.Fi24F4

end
