module

public import Certificates.Kernel.J4Q.Mask
public import Certificates.Kernel.J4Q.MaskData
public import CFSG.Sporadic.J4.QTRankNative
public import CFSG.Certificates.Kernel.Spor.Loops
import Certificates.Kernel.J4Q.Strs
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.J4Q.Orbits

public section

set_option maxRecDepth 400000

#j4q_strs CFSG.KD.J4Q.KW CFSG.Sporadic.J4.QT.kWords

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.QT

@[expose] noncomputable def mkKW : List (List Int) :=
  [lettersK KW.s0, lettersK KW.s1, lettersK KW.s2, lettersK KW.s3]

theorem kWords_eq : kWords = mkKW := by
  rw [KW.eq]
  simp only [List.map_cons, List.map_nil, lettersOfString_ofList]
  rfl

theorem mkKT_chk : decide (∀ i ∈ List.range 4, wordT (mkKW.getD i []) = mkKT.getD i [] ∧
    wordT (invWord (mkKW.getD i [])) = mkKIT.getD i []) = true := by
  quickRfl

theorem kTab_eq {i : Nat} (hi : i < 4) : kTab i = mkKT.getD i [] := by
  rw [kTab, kWords_eq]
  exact ((of_decide_eq_true mkKT_chk) i (List.mem_range.2 hi)).1

theorem kInvTab_eq {i : Nat} (hi : i < 4) : kInvTab i = mkKIT.getD i [] := by
  rw [kInvTab, kWords_eq]
  exact ((of_decide_eq_true mkKT_chk) i (List.mem_range.2 hi)).2

theorem pcSeq_lt_chk : decide (∀ e ∈ List.range 1024, ∀ i ∈ pcSeq e, i < 4) = true := by quickRfl

theorem pcSeq_lt : ∀ e < 1024, ∀ i ∈ pcSeq e, i < 4 :=
  fun e he => of_decide_eq_true pcSeq_lt_chk e (List.mem_range.2 he)

theorem e_split (e : Nat) : 32 * (e / 32) + e % 32 = e := Nat.div_add_mod e 32

theorem div32_lt {e : Nat} (he : e < 1024) : e / 32 < 32 := Nat.div_lt_of_lt_mul (by omega)

theorem chunk_spec {f : Nat → Nat → Bool} (h : ∀ k < 32, CFSG.KC.Enum.allN 32 (f k) = true)
    {e : Nat} (he : e < 1024) : f (e / 32) (e % 32) = true :=
  CFSG.KS.allN_spec (h (e / 32) (div32_lt he)) (e % 32) (Nat.mod_lt _ (by decide))

@[expose] def mkSeq (s : List Nat) : List Nat := (s.map fun i => mkKT.getD i []).foldr compT idT

theorem seqT_eq {s : List Nat} (hs : ∀ i ∈ s, i < 4) : seqT s = mkSeq s := by
  unfold seqT mkSeq
  rw [List.map_congr_left fun i hi => kTab_eq (hs i hi)]

@[expose] noncomputable def mkTLc (k : Nat) : Bool :=
  CFSG.KC.Enum.allN 32 fun j => decide (mkSeq (pcSeq (32 * k + j)) = mkTL.getD (32 * k + j) [])

#j4q_all CFSG.KD.J4Q.TLC CertificateChecks.KernelJ4Q.mkTLc 32

theorem mkTL_length : mkTL.length = 1024 := by
  rw [← lenK_eq]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem tab_eq {e : Nat} (he : e < 1024) : seqT (pcSeq e) = mkTL.getD e [] := by
  rw [seqT_eq (pcSeq_lt e he)]
  have h := chunk_spec (f := fun k j => decide (mkSeq (pcSeq (32 * k + j)) = mkTL.getD (32 * k + j) []))
    TLC.all he
  simp only [e_split] at h
  exact of_decide_eq_true h

theorem tabL_eq : tabL = mkTL := by
  apply List.ext_getElem
  · rw [mkTL_length]
    simp [tabL]
  · intro e h1 h2
    have he : e < 1024 := by simpa [tabL] using h1
    simp only [tabL, List.getElem_map, List.getElem_range]
    rw [tab_eq he, List.getD_eq_getElem _ _ h2]

theorem mem_mkTL {t : List Nat} (h : t ∈ mkTL) : ∃ e < 1024, t = mkTL.getD e [] := by
  obtain ⟨e, he, rfl⟩ := List.getElem_of_mem h
  exact ⟨e, mkTL_length ▸ he, (List.getD_eq_getElem _ _ he).symm⟩

theorem getD_mem_mkTL {e : Nat} (he : e < 1024) : mkTL.getD e [] ∈ mkTL := by
  rw [List.getD_eq_getElem _ _ (mkTL_length ▸ he)]
  exact List.getElem_mem _

end CertificateChecks.KernelJ4Q

end
