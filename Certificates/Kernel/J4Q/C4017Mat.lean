module

public import Certificates.Kernel.J4Q.MaskRep
public import Certificates.Kernel.J4Q.Mask
import Certificates.Kernel.J4Q.Strs
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.J4Q.Orbits
public import Certificates.Kernel.J4Q.QTBase

public section

set_option maxRecDepth 400000

#j4q_strs CFSG.KD.J4Q.XPW CFSG.Sporadic.J4.QT.xpWord

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.Loop CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT

theorem u_enc {i : Nat} (hi : i < 11) :
    WfA ((uTab (locMats ()) (locInvs ()))[i]?.getD (idRows ())) ∧
      encR ((uTab (locMats ()) (locInvs ()))[i]?.getD (idRows ())) = getN one Us i :=
  uTab_enc i hi

theorem u_chk' : (List.range 11).all (fun i => Nat.beq (mulJ c rm (getN one Us i) (getN one Us i)) one &&
    (List.range 11).all fun j => Nat.beq (mulJ c rm (getN one Us i) (getN one Us j))
      (mulJ c rm (getN one Us j) (getN one Us i))) = true := by
  quickRfl

theorem chkU_ok : chkU (locMats ()) (locInvs ()) = true := by
  unfold chkU
  simp only []
  rw [mkRange_congr fun i hi => by
    rw [mkEq (mkMul (u_enc hi) (u_enc hi)) mkId, mkRange_congr fun j hj => by
      rw [mkEq (mkMul (u_enc hi) (u_enc hj)) (mkMul (u_enc hj) (u_enc hi))]]]
  exact u_chk'

theorem c4017_xR_enc (ℓ : Int) : WfA (xRows (locMats ()) (locInvs ()) ℓ) ∧
    encR (xRows (locMats ()) (locInvs ()) ℓ) = letJ one [L0, L1, L2] [L0i, L1i, L2i] ℓ :=
  letter_enc loc_gens loc_invs ℓ

theorem xiR_enc (ℓ : Int) : WfA (xiRows (locMats ()) (locInvs ()) ℓ) ∧
    encR (xiRows (locMats ()) (locInvs ()) ℓ) = letJ one [L0i, L1i, L2i] [L0, L1, L2] ℓ :=
  letter_enc loc_invs loc_gens ℓ

theorem conj_chk' : letters.all (fun ℓ => (List.range 11).all fun j =>
    Nat.beq (mulJ c rm (mulJ c rm (letJ one [L0, L1, L2] [L0i, L1i, L2i] ℓ) (getN one Us j))
      (letJ one [L0i, L1i, L2i] [L0, L1, L2] ℓ)) (etaK c rm one Us (letterRow ℓ j))) = true := by
  quickRfl

theorem chkConj_ok : chkConj (locMats ()) (locInvs ()) = true := by
  unfold chkConj
  simp only []
  rw [mkAll_congr fun ℓ _ => mkRange_congr fun j hj => by
    rw [mkEq (mkMul (mkMul (c4017_xR_enc ℓ) (u_enc hj)) (xiR_enc ℓ)) (eta_enc _)]]
  exact conj_chk'

@[expose] noncomputable def mkVE (c : Nat) : Nat :=
  (List.range 11).foldl (fun a j => if c.testBit j then vecJ rm a (getN one Us j) else a) (v2N w0)

theorem c4017_w0_wf : w0.wf = true := by decide

theorem F_get {j : Nat} (hj : j < 11) :
    ((uTab (locMats ()) (locInvs ())).map frTable)[j]?.getD #[] =
      frTable ((uTab (locMats ()) (locInvs ()))[j]?.getD (idRows ())) := by
  have hs : j < (uTab (locMats ()) (locInvs ())).size := by simp [uTab, hj]
  simp [hs]

theorem etaVec_fold (c : Nat) : ∀ (L : List Nat), (∀ j ∈ L, j < 11) → ∀ (acc : V2) (a : Nat),
    acc.wf = true → v2N acc = a →
    (L.foldl (fun acc j => if c.testBit j then
        frApply (((uTab (locMats ()) (locInvs ())).map frTable)[j]?.getD #[]) acc else acc) acc).wf = true ∧
      v2N (L.foldl (fun acc j => if c.testBit j then
        frApply (((uTab (locMats ()) (locInvs ())).map frTable)[j]?.getD #[]) acc else acc) acc) =
        L.foldl (fun a j => if c.testBit j then vecJ rm a (getN one Us j) else a) a
  | [], _, _, _, hw, hv => ⟨hw, hv⟩
  | j :: L, hL, acc, a, hw, hv => by
    have hj := hL j List.mem_cons_self
    have hL' : ∀ i ∈ L, i < 11 := fun i hi => hL i (List.mem_cons_of_mem _ hi)
    rw [List.foldl_cons, List.foldl_cons]
    by_cases hb : c.testBit j
    · simp only [hb, ↓reduceIte]
      rw [F_get hj]
      exact etaVec_fold c L hL' _ _ (wf_frApply (u_enc hj).1 _)
        (by rw [v2N_frApply hK (u_enc hj).1 hw, (u_enc hj).2, hv])
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      exact etaVec_fold c L hL' acc a hw hv

theorem c4017_etaVec_enc (c : Nat) :
    (etaVec ((uTab (locMats ()) (locInvs ())).map frTable) 11 c).wf = true ∧
      v2N (etaVec ((uTab (locMats ()) (locInvs ())).map frTable) 11 c) = mkVE c :=
  etaVec_fold c (List.range 11) (fun _ hj => List.mem_range.1 hj) w0 _ c4017_w0_wf rfl

@[expose] noncomputable def mkFRc (k : Nat) : Bool :=
  CFSG.KC.Enum.allN 32 fun j => (32 * k + j == 0 || neN (mkVE (32 * k + j)) (v2N w0))

#j4q_all CFSG.KD.J4Q.FRC CertificateChecks.KernelJ4Q.mkFRc 64

theorem chkFree_ok : chkFree (locMats ()) (locInvs ()) = true := by
  unfold chkFree
  simp only []
  refine List.all_eq_true.2 fun c hc => ?_
  have hc' : c < 32 * 64 := by simpa using hc
  have h := mkChunk (f := fun k j => (32 * k + j == 0 || neN (mkVE (32 * k + j)) (v2N w0))) FRC.all hc'
  simp only [mkSplit] at h
  rw [differs_eq (c4017_etaVec_enc c).1 c4017_w0_wf, (c4017_etaVec_enc c).2]
  exact h

@[expose] noncomputable def mkXPW : List Int := lettersK XPW.s0

theorem xpWord_eq : xpWord = mkXPW := by
  rw [XPW.eq]
  exact lettersOfString_ofList _

theorem xp_enc : WfA (xpRows (locMats ()) (locInvs ())) ∧ encR (xpRows (locMats ()) (locInvs ())) =
    wordJ c rm one [L0, L1, L2] [L0i, L1i, L2i] mkXPW := by
  have h := enc_wordRows hK loc_gens loc_invs xpWord
  rw [xpWord_eq] at h
  exact h

@[expose] noncomputable def mkY : Nat := vecJ rm (v2N w0) (wordJ c rm one [L0, L1, L2] [L0i, L1i, L2i] mkXPW)

@[expose] noncomputable def mkOTc (k : Nat) : Bool :=
  CFSG.KC.Enum.allN 32 fun j => neN (mkVE (32 * k + j)) mkY

#j4q_all CFSG.KD.J4Q.OTC CertificateChecks.KernelJ4Q.mkOTc 64

theorem chkOut_ok : chkOut (locMats ()) (locInvs ()) = true := by
  unfold chkOut
  simp only []
  refine List.all_eq_true.2 fun c hc => ?_
  have hc' : c < 32 * 64 := by simpa using hc
  have h := mkChunk (f := fun k j => neN (mkVE (32 * k + j)) mkY) OTC.all hc'
  simp only [mkSplit] at h
  rw [differs_eq (c4017_etaVec_enc c).1 (wf_frApply xp_enc.1 _), (c4017_etaVec_enc c).2,
    v2N_frApply hK xp_enc.1 c4017_w0_wf, xp_enc.2]
  exact h

theorem fus_chk' : (Nat.beq (mulJ c rm (wordJ c rm one [L0, L1, L2] [L0i, L1i, L2i] mkXPW)
    (wordJ c rm one [L0, L1, L2] [L0i, L1i, L2i] mkXPW)) one &&
    Nat.beq (powJ c rm one (mulJ c rm (mulJ c rm (mulJ c rm A (getN one Us 0)) A)
      (wordJ c rm one [L0, L1, L2] [L0i, L1i, L2i] mkXPW)) 33) one) = true := by
  quickRfl

theorem chkFus_ok : chkFus (locMats ()) (locInvs ()) = true := by
  unfold chkFus
  simp only []
  rw [mkEq (mkMul xp_enc xp_enc) mkId,
    mkEq (mkPow (mkMul (mkMul (mkMul rowsA_enc (u_enc (i := 0) (by decide))) rowsA_enc) xp_enc) 33) mkId]
  exact fus_chk'

end CertificateChecks.KernelJ4Q

end
