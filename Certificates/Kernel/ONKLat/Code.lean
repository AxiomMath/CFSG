module

public import CFSG.Certificates.Kernel.Misc.PermClosWSound
public import CFSG.Certificates.Kernel.Spor.CBfsKSound
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporONCheckInputs
public import Certificates.Kernel.ONKLat.Data

public section

namespace CertificateChecks.KernelSpor.ONKL

open Equiv CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.ONSchreier CFSG.ONSchreier.Native
  CFSG.KC.Misc.ClosW CFSG.ComponentClassification.PSL3Four
  CFSG.LocalAnalysis.UniquenessCase.UC22.F10.ONK

theorem unpack_getD {n w P i : ℕ} (hi : i < n) : (unpack n w P)[i]! = pg w (mask w) P i := by
  unfold unpack
  rw [getElem!_ofFn_nat _ hi]

theorem wcode_of_fld {n w P : ℕ} {g : Perm (Fin n)} (hw : n + 1 < 2 ^ w)
    (h0 : P >>> (n * w) = 0) (h : ∀ i : Fin n, pg w (mask w) P i = g i) : wcode w g = P :=
  PF.eq_of_fields (PF.w_pos hw) (wcode_shr hw g) h0 fun i hi => by
    rw [pg_wcode_nat (by omega) g hi]
    exact (h ⟨i, hi⟩).symm

theorem wcode_of_tab {n w P : ℕ} {g : Perm (Fin n)} (hw : n + 1 < 2 ^ w)
    (h0 : P >>> (n * w) = 0) (ht : TabRep (unpack n w P) g) : wcode w g = P :=
  wcode_of_fld hw h0 fun i => by
    rw [← unpack_getD i.2]
    exact ht.2 i

theorem wcode_of_prep {n w P : ℕ} {g : Perm (Fin n)} (hw : n + 1 < 2 ^ w)
    (h0 : P >>> (n * w) = 0) (ht : PRep n (unpack n w P) g) : wcode w g = P :=
  wcode_of_fld hw h0 fun i => by
    rw [← unpack_getD i.2]
    exact ht i

theorem shr_of_canon {n w P : ℕ} (h : canonK n w (mask w) (n * w) P = true) :
    P >>> (n * w) = 0 :=
  (PF.canon_facts h).2.2.1

theorem pisInv_inv_of {n w P : ℕ}
    (hf : ∀ x < n, pg w (mask w) P x < n ∧ pg w (mask w) P (pg w (mask w) P x) = x) :
    pisInv n (unpack n w P) (pinvCand n (unpack n w P)) = true ∧
      pisInv n (pinvCand n (unpack n w P)) (unpack n w P) = true := by
  have ht : ∀ y < n, (unpack n w P)[y]! = pg w (mask w) P y := fun y hy => unpack_getD hy
  have hg : ∀ y < n, (pinvCand n (unpack n w P))[y]! = pg w (mask w) P y := fun y hy =>
    CFSG.KS.CB.pinvCand_get (T := fun i => pg w (mask w) P i) (U := fun i => pg w (mask w) P i)
      (fun x hx => (hf x hx).1) (fun x hx => (hf x hx).2) hy
  constructor
  · unfold pisInv
    refine allBelowN_iff.2 fun x hx => ?_
    rw [ht x hx, hg _ (hf x hx).1, (hf x hx).2]
    simp [(hf x hx).1]
  · unfold pisInv
    refine allBelowN_iff.2 fun x hx => ?_
    rw [hg x hx, ht _ (hf x hx).1, (hf x hx).2]
    simp [(hf x hx).1]

theorem prep_onKPerm_inv {n w P : ℕ}
    (hf : ∀ x < n, pg w (mask w) P x < n ∧ pg w (mask w) P (pg w (mask w) P x) = x) :
    PRep n (unpack n w P) (onKPerm n (unpack n w P)) := fun x => by
  rw [onKPerm, dif_pos (pisInv_inv_of hf)]
  rfl

theorem henc120 : CFSG.KC.Misc.Clos.ClosEnc (wcode (n := 120) 7) (pcomp 120 7 (mask 7))
    (pidn 120 7) := wcode_enc (by norm_num) (by norm_num)

theorem henc32 : CFSG.KC.Misc.Clos.ClosEnc (wcode (n := 32) 6) (pcomp 32 6 (mask 6))
    (pidn 32 6) := wcode_enc (by norm_num) (by norm_num)

theorem beq_code {n w : ℕ} {M : ℕ → ℕ → ℕ} {one : ℕ}
    (he : CFSG.KC.Misc.Clos.ClosEnc (wcode (n := n) w) M one) {a b : Perm (Fin n)} :
    Nat.beq (wcode w a) (wcode w b) = true ↔ a = b := by
  rw [Nat.beq_eq]
  exact ⟨fun h => he.inj h, fun h => h ▸ rfl⟩

end CertificateChecks.KernelSpor.ONKL

end
