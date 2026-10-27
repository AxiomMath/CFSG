module

public import CFSG.Sporadic.J4.QTRankInvNative
public import Certificates.Kernel.J4Q.MaskBlk
public import Certificates.Kernel.J4Q.MaskRep
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.J4Q.QTBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.Loop CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT

@[expose] noncomputable def mkKMs : List Nat := [mkKM_0, mkKM_1, mkKM_2, mkKM_3]

theorem km_chk : decide (∀ i ∈ List.range 4, getN one mkKMs i =
    wordJ c rm one [L0, L1, L2] [L0i, L1i, L2i] (mkKW.getD i [])) = true := by
  quickRfl

theorem kRows_enc {i : Nat} (hi : i < 4) : WfA (kRows i) ∧ encR (kRows i) = getN one mkKMs i := by
  have h := enc_wordRows hK loc_gens loc_invs (kWords.getD i [])
  rw [kWords_eq] at h
  exact ⟨h.1, h.2.trans (of_decide_eq_true km_chk i (List.mem_range.2 hi)).symm⟩

theorem kTab_get {i : Nat} (hi : i < 4) : (kRowsTab ())[i]?.getD (idRows ()) = kRows i := by
  simp [kRowsTab, hi]

@[expose] noncomputable def mkKe (e : Nat) : Nat :=
  (pcSeq e).foldl (fun a i => mulJ c rm a (getN one mkKMs i)) one

theorem fold_enc : ∀ (s : List Nat), (∀ i ∈ s, i < 4) → ∀ (acc : Array V2) (a : Nat),
    WfA acc ∧ encR acc = a →
    WfA (s.foldl (fun acc i => mulRows acc ((kRowsTab ())[i]?.getD (idRows ()))) acc) ∧
      encR (s.foldl (fun acc i => mulRows acc ((kRowsTab ())[i]?.getD (idRows ()))) acc) =
        s.foldl (fun a i => mulJ c rm a (getN one mkKMs i)) a
  | [], _, _, _, h => h
  | i :: s, hs, acc, a, h => by
    have hi := hs i List.mem_cons_self
    have hk := kRows_enc hi
    rw [← kTab_get hi] at hk
    exact fold_enc s (fun j hj => hs j (List.mem_cons_of_mem _ hj)) _ _ (mkMul h hk)

theorem kel_enc {e : Nat} (he : e < 1024) :
    WfA (KelRowsK (kRowsTab ()) e) ∧ encR (KelRowsK (kRowsTab ()) e) = mkKe e :=
  fold_enc (pcSeq e) (pcSeq_lt e he) _ _ ⟨wf_idRows, enc_idRows hK⟩

@[expose] noncomputable def mkGM (g : Nat) : Nat := getN one [A, B, Bi] g

@[expose] noncomputable def mkGI (g : Nat) : Nat := getN one [Ai, Bi, B] g

theorem gMat_enc (g : Nat) : WfA (gMat g) ∧ encR (gMat g) = mkGM g := by
  rcases g with _ | _ | _ | g
  · exact base_gens 0
  · exact base_gens 1
  · exact base_invs 1
  · have h : gMat (g + 3) = baseMats[g + 3]?.getD (idRows ()) := by simp [gMat]
    rw [h]
    exact base_gens (g + 3)

theorem gInv_enc (g : Nat) : WfA (gInv g) ∧ encR (gInv g) = mkGI g := by
  rcases g with _ | _ | _ | g
  · exact base_invs 0
  · exact base_invs 1
  · exact base_gens 1
  · have h : gInv (g + 3) = baseInvs[g + 3]?.getD (idRows ()) := by simp [gInv]
    rw [h]
    exact base_invs (g + 3)

@[expose] noncomputable def mkFuse (Ke : Nat) (y : Nat × Nat × Nat × Nat) : Bool :=
  decide (y.2.1 < 3) && decide (0 < y.2.2.1) && decide (y.2.2.1 < 2048) && y.2.2.2 % 2 == 1 &&
    Nat.beq (powJ c rm one (mulJ c rm (mulJ c rm (etaK c rm one Us y.1) Ke)
      (mulJ c rm (mulJ c rm (mkGM y.2.1) (etaK c rm one Us y.2.2.1)) (mkGI y.2.1))) y.2.2.2) one

theorem fuse_eq {e : Nat} (he : e < 1024) (y : Nat × Nat × Nat × Nat) :
    fuseOKT (uTab (locMats ()) (locInvs ())) (kRowsTab ()) e y = mkFuse (mkKe e) y := by
  unfold fuseOKT mkFuse etaRT
  simp only []
  rw [mkEq (mkPow (mkMul (mkMul (eta_enc _) (kel_enc he))
    (mkMul (mkMul (gMat_enc _) (eta_enc _)) (gInv_enc _))) _) ⟨wf_idRows, enc_idRows hK⟩]

@[expose] noncomputable def mkIm (t : List Nat) : List Nat :=
  (List.range 2048).map fun m => m ^^^ actN 11 t m

@[expose] noncomputable def mkCover (x : Nat × Nat × List (Nat × Nat × Nat × Nat)) : Bool :=
  strictB (mkSet (mkIm (tabAt x.1))) fun S => (List.range 2048).all fun c =>
    c ^^^ actN 11 (tabAt x.1) c != x.2.1 || x.2.2.any fun y => bitB S (c ^^^ y.1)

theorem cover_eq {x : Nat × Nat × List (Nat × Nat × Nat × Nat)} (h : x.1 < 1024) :
    classCover x = mkCover x := by
  unfold classCover mkCover imSet tabE
  rw [tab_eq h, mkStrictB_eq, tabAt_eq h]
  simp only [actT_eq, contains_eraseDups, mkIm]

@[expose] noncomputable def mkInv (x : Nat × Nat × List (Nat × Nat × Nat × Nat)) : Bool :=
  decide (x.1 < 1024) && decide (x.2.1 < 2048) && strictB (mkKe x.1) fun k =>
    Nat.beq (mulJ c rm k k) (etaK c rm one Us x.2.1) && mkCover x && x.2.2.all (mkFuse k)

theorem inv_eq (x : Nat × Nat × List (Nat × Nat × Nat × Nat)) :
    invOKT (uTab (locMats ()) (locInvs ())) (kRowsTab ()) x = mkInv x := by
  by_cases h : x.1 < 1024
  · have hf : fuseOKT (uTab (locMats ()) (locInvs ())) (kRowsTab ()) x.1 = mkFuse (mkKe x.1) :=
      funext (fuse_eq h)
    unfold invOKT mkInv etaRT
    rw [mkStrictB_eq, mkEq (mkMul (kel_enc h) (kel_enc h)) (eta_enc _), cover_eq h, hf]
    simp only [Bool.and_assoc]
  · simp [invOKT, mkInv, h]

@[expose] noncomputable def mkInvK (k : Nat) : Bool := mkInv (invData.getD k (0, 0, []))

#j4q_all CFSG.KD.J4Q.IVC CertificateChecks.KernelJ4Q.mkInvK 191

theorem invData_length : invData.length = 191 := by
  rw [← lenK_eq]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem invAll_ok : invAllOK = true := by
  unfold invAllOK
  simp only []
  rw [funext inv_eq, List.all_eq_true]
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  have hk' : k < 191 := by
    rw [← invData_length]
    exact hk
  have h := IVC.all k hk'
  unfold mkInvK at h
  rwa [List.getD_eq_getElem _ _ hk] at h

@[expose] noncomputable def mkII (k j : Nat) : Bool :=
  !(compN (tabAt (32 * k + j)) (tabAt (32 * k + j)) == idT && tabAt (32 * k + j) != idT) ||
    invData.any fun x => x.1 == 32 * k + j

@[expose] noncomputable def mkIIc (k : Nat) : Bool := CFSG.KC.Enum.allN 32 (mkII k)

#j4q_all CFSG.KD.J4Q.IIC CertificateChecks.KernelJ4Q.mkIIc 32

theorem c4025_orbits_chk : decide (∀ o ∈ orbits, o.1 = 1 ∨ o.1 = 3) = true := by quickRfl

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT in
theorem c4025 : (invAllOK = true)
    ∧ (∀ e < 1024, isInvE e = true → ∃ x ∈ invData, x.1 = e)
    ∧ (∀ o ∈ orbits, o.1 = 1 ∨ o.1 = 3) := by
  refine ⟨invAll_ok, fun e he h => ?_, of_decide_eq_true c4025_orbits_chk⟩
  unfold isInvE tabE at h
  rw [tab_eq he, ← tabAt_eq he, compT_eq] at h
  have h2 := mkChunkW (w := 32) (n := 32) (f := mkII) IIC.all (e := e) he
  unfold mkII at h2
  simp only [mkSplitW] at h2
  rw [h, Bool.not_true, Bool.false_or, List.any_eq_true] at h2
  obtain ⟨x, hx, hxe⟩ := h2
  exact ⟨x, hx, beq_iff_eq.1 hxe⟩

end CertificateChecks.KernelJ4Q

end
