
module

public import Certificates.Kernel.SporSch.Co2M.EnumR
public import Certificates.Kernel.SporSch.Co2M.KerSS
public import CFSG.Sporadic.Co2Schreier.KerCheckInputs
public meta import Certificates.Kernel.SporSch.Co2M.EnumGen
public meta import CFSG.Sporadic.Co2Schreier.KerCheckInputs
public meta import CFSG.Sporadic.Co2Cert.Data
meta import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.Load

public section

set_option maxRecDepth 400000
set_option exponentiation.threshold 600

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2.Native

meta def kerSift : Array (Array Nat) :=
  #[(extendArrs dArrs localRec.chains.D.derivations)[6]!,
    (extendArrs dArrs localRec.chains.D.derivations)[7]!,
    (extendArrs dArrs localRec.chains.D.derivations)[8]!,
    wordArr dArrs (witRec.wLocal.dAdditionalFixedWords.getD 0 [])]

meta def kerSiftRows : Array (Array Nat) :=
  kerSift.map fun a => Gen.rowsOf (Gen.matOf vecsM (Gen.basisOf vecsM) a)

end CertificateChecks.KernelSporSch.Co2M

#kc_items CertificateChecks.KernelSporSch.Co2M.KSG include_bytes "data/Ker.KSG.items" 13816 7890775224598703555
#kc_items CertificateChecks.KernelSporSch.Co2M.KSM include_bytes "data/Ker.KSM.items" 258 4253814945973152939

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2M CFSG.KS.Co2LE CFSG.KS.MatRep CFSG.KS.MatInj
open CFSG.RankThree.Native.F2 CFSG.Monster.B.Mathieu
open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2.Native

@[expose] noncomputable def P484 : ℕ := nat_lit 49947976805055875702105555676690660891977570282639538413746511354005947821116249921924897649015871538557230897942505966327167610868612564900642816

theorem P484_eq : P484 = 2 ^ (22 * 22) := by decide

@[expose] noncomputable def md (X : ℕ) : ℕ := Nat.mod X P484

@[expose] noncomputable def ZM (k : ℕ) : ℕ := eM RR (centerIdxR.getD k 0)

@[expose] noncomputable def dTL : List (ℕ × ℕ) := [(RC 0, RC 2), (RC 1, RC 3)]

@[expose] noncomputable def candT (k0 k1 : ℕ) : List (ℕ × ℕ) :=
  [cmpP (RC 0, RC 2) (ZM k0, ZM k0), cmpP (RC 1, RC 3) (ZM k1, ZM k1)]

@[expose] def derivD : List (List ℤ) := localRec.chains.D.derivations

@[expose] def addW : List ℤ := witRec.wLocal.dAdditionalFixedWords.getD 0 []

@[expose] noncomputable def candK (k0 k1 : ℕ) : Bool :=
  ([6, 7, 8] : List ℕ).all (fun j => Nat.beq (md ((extP mmK I22 (candT k0 k1) derivD).getD j (0, 0)).1)
      (KSM (j - 6))) &&
    allN 10 (fun i => Nat.beq (md (wP (extP mmK I22 (candT k0 k1) localRec.dStrongDerivations)
      (localRec.rWords.getD i [])).1) (md (RG i))) &&
    ([addW] : List (List ℤ)).all (fun w => Nat.beq (md (wP (candT k0 k1) w).1) (KSM 3))

theorem zinv_ok : allN 32 (fun k => Nat.beq (mmK (ZM k) (ZM k)) I22) = true := by quickRfl

theorem ksm_ok : allN 3 (fun i => Nat.beq (KSM i)
    (md ((extP mmK I22 dTL derivD).getD (Nat.add 6 i) (0, 0)).1)) = true ∧
    Nat.beq (KSM 3) (md (wP dTL addW).1) = true := by
  constructor <;> decide +kernel

theorem ksg_bind : allN 3 (fun i => bindK (PV 0) (KSG i)
    ((extP mmK I22 dTL derivD).getD (Nat.add 6 i) (0, 0)).1
    ((extP mmK I22 dTL derivD).getD (Nat.add 6 i) (0, 0)).2) = true ∧
    bindK (PV 0) (KSG 3) (wP dTL addW).1 (wP dTL addW).2 = true := by
  constructor <;> decide +kernel

theorem ksg_range : allN 4 (fun i => allN 2300 (fun p => Nat.blt (pg 12 (mask 12) (KSG i) p) 2300)) =
    true := by quickRfl

theorem ksg_sift : allN 4 (fun i => siftK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) Co2SS.LR
    Co2SS.TRI Co2SS.BP 3 0 (KSG i)) = true := by quickRfl

theorem dz_ok : (Nat.beq (md (cmpP (RC 0, RC 2) zP).1) (md (cmpP zP (RC 0, RC 2)).1) &&
    !Nat.beq (md (cmpP (RC 1, RC 3) zP).1) (md (cmpP zP (RC 1, RC 3)).1) &&
    Nat.beq (md (cmpP zP (RC 1, RC 3)).1) (md (cmpP (cmpP (RC 1, RC 3) (ZM 9, ZM 9)) zP).1)) =
    true := by
  decide +kernel

theorem words_ok : (extWordsOK 2 derivD && extWordsOK 2 localRec.dStrongDerivations &&
    localRec.rWords.all (lettersOK (2 + localRec.dStrongDerivations.length)) &&
    witRec.wLocal.dAdditionalFixedWords.all (lettersOK 2) &&
    extOK 2 derivD && extOK 2 localRec.dStrongDerivations &&
    witRec.wLocal.dStrongFixedBySIndices == [6, 7, 8] &&
    witRec.wLocal.dAdditionalFixedWords == [addW] &&
    witRec.wLocal.dCandidateSurvivors == [[0, 0], [0, 9]] &&
    derivD.length == 10 && localRec.dStrongDerivations.length == 5 &&
    localRec.rWords.length == 10 && allN 32 (fun k => Nat.blt (centerIdxR.getD k 0) 2048) &&
    centerIdxR.length == 32 && centerIdxR.getD 0 0 == 0) = true := by
  decide +kernel

theorem V_size' : co2PackedVecs.size = 2300 := V_size

theorem eqA_rep {a b : Array ℕ} {X X' Y Y' : ℕ} (ha : Rep 22 co2PackedVecs a X X')
    (hb : Rep 22 co2PackedVecs b Y Y') : eqA 2300 a b = Nat.beq (md X) (md Y) := by
  rw [ha.1, hb.1, ← V_size, eqA_permOfMat_mod spans ha.2.1 hb.2.1, md, md, P484_eq]
  rfl

theorem allInv_of {A : Array (Array ℕ)} {T : List (ℕ × ℕ)} (hT : RepT 22 co2PackedVecs A T) :
    allInv A = true := by
  unfold allInv
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro j hj
  have h := hT.2 j (by rw [← hT.1]; exact hj)
  rw [h.1, ← V_size, invCand_permOfMat good.hd good.nodup good.lt h.2]
  exact isInvA_permOfMat good.hd good.nodup good.lt h.2

theorem dRepL : RepT 22 co2PackedVecs dArrs dTL := by
  refine ⟨by rw [dRep.1, d_len]; rfl, fun k hk => ?_⟩
  have hk2 : k < 2 := hk
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · exact rcrep 0 (by norm_num)
  · exact rcrep 1 (by norm_num)

theorem zs_get {k : ℕ} (hk : k < 32) :
    kerData.zs[k]! = enumR.elems[centerIdxR.getD k 0]! := by
  have hl : centerIdxR.length = 32 := rfl
  unfold kerData
  dsimp only
  rw [getElem!_pos _ k (by simp [hl]; omega)]
  simp only [List.getElem_toArray, List.getElem_map, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [hl]; exact hk : k < centerIdxR.length), Option.getD_some]

theorem zsRep {k : ℕ} (hk : k < 32) : Rep 22 co2PackedVecs kerData.zs[k]! (ZM k) (ZM k) := by
  have hc : centerIdxR.getD k 0 < 2048 := by
    have h := words_ok
    simp only [Bool.and_eq_true] at h
    have := allN_spec h.1.1.2 k hk
    rwa [Nat.blt_eq] at this
  obtain ⟨M', hM⟩ := enumR_rep _ hc
  rw [zs_get hk]
  have hz := Nat.eq_of_beq_eq_true (allN_spec zinv_ok k hk)
  rw [mmK_eq, I22_eq] at hz
  exact rep_of_inv good.hd good.lt hM hz hz

theorem candRep {k0 k1 : ℕ} (h0 : k0 < 32) (h1 : k1 < 32) :
    RepT 22 co2PackedVecs (candArrs kerData k0 k1) (candT k0 k1) := by
  have hd0 : Rep 22 co2PackedVecs kerData.d[0]! (RC 0) (RC 2) := rcrep 0 (by norm_num)
  have hd1 : Rep 22 co2PackedVecs kerData.d[1]! (RC 1) (RC 3) := rcrep 1 (by norm_num)
  have a0 : ∀ K : KerData, (candArrs K k0 k1)[0]! = compA 2300 K.d[0]! K.zs[k0]! := fun _ => rfl
  have a1 : ∀ K : KerData, (candArrs K k0 k1)[1]! = compA 2300 K.d[1]! K.zs[k1]! := fun _ => rfl
  have t0 : (candT k0 k1).getD 0 (0, 0) = cmpP (RC 0, RC 2) (ZM k0, ZM k0) := rfl
  have t1 : (candT k0 k1).getD 1 (0, 0) = cmpP (RC 1, RC 3) (ZM k1, ZM k1) := rfl
  have hs : ∀ K : KerData, (candArrs K k0 k1).size = 2 := fun _ => rfl
  refine ⟨by rw [hs]; rfl, fun k hk => ?_⟩
  have hk2 : k < 2 := hk
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · rw [a0, t0]
    exact rep_cmp hd0 (zsRep h0)
  · rw [a1, t1]
    exact rep_cmp hd1 (zsRep h1)

theorem extP_length (T : List (ℕ × ℕ)) (ds : List (List ℤ)) :
    (extP mmK I22 T ds).length = T.length + ds.length := by
  unfold extP
  induction ds generalizing T with
  | nil => simp
  | cons w ds ih =>
    rw [List.foldl_cons, ih]
    simp
    omega

theorem all_congr' {α : Type} {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem allLt_congr' {n : ℕ} {f g : ℕ → Bool} (h : ∀ i < n, f i = g i) : allLt n f = allN n g := by
  rw [Bool.eq_iff_iff, CFSG.Monster.B.Co2.allLt_iff]
  exact ⟨fun hf => CFSG.KS.Raw.allN_of_forall fun i hi => by rw [← h i hi]; exact hf i hi,
    fun hg i hi => by rw [h i hi]; exact allN_spec hg i hi⟩

theorem wfacts : extOK 2 derivD = true ∧ extOK 2 localRec.dStrongDerivations = true ∧
    kerData.fixedIdx = [6, 7, 8] ∧ kerData.addWords = [addW] ∧
    kerData.survivors = [[0, 0], [0, 9]] ∧ kerData.rWords.length = 10 ∧
    (∀ i < 10, lettersOK 7 (localRec.rWords.getD i []) = true) ∧ lettersOK 2 addW = true ∧
    extWordsOK 2 kerData.derivD = true ∧ extWordsOK 2 kerData.derivLegacy = true ∧
    kerData.rWords.all (lettersOK (2 + kerData.derivLegacy.length)) = true ∧
    kerData.addWords.all (lettersOK 2) = true := by
  have h := words_ok
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, -⟩,
    -⟩ := h
  have hrw : ∀ i < 10, lettersOK 7 (localRec.rWords.getD i []) = true := by
    intro i hi
    have h3' := h3
    rw [h11] at h3'
    rw [List.getD_eq_getElem _ _ (by rw [h12]; exact hi)]
    exact List.all_eq_true.1 h3' _ (List.getElem_mem _)
  have hadd : lettersOK 2 addW = true := by
    have h4' := h4
    rw [h8] at h4'
    simpa using h4'
  exact ⟨h5, h6, h7, h8, h9, h12, hrw, hadd, h1, h2, h3, h4⟩

end CertificateChecks.KernelSporSch.Co2M

end
