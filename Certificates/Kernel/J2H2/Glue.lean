module

public import Certificates.Kernel.J2H2.Checks1
public import Certificates.Kernel.J2H2.Checks2
public import Certificates.Kernel.J2H2.Checks3
public import CFSG.Certificates.Kernel.J2H2.Sound2
public import CFSG.Certificates.Kernel.PackSetSound
public import Certificates.Kernel.J2Cover.ModelsBind

public section

namespace CertificateChecks.J2H2

open CFSG.KD.J2H2 CFSG.KC.Enum CFSG.KC.J2H2
open CFSG.ComponentClassification.J2Cover.Models CFSG.RankThree.PartTwo.J2Residue.H2
open CFSG.RankThree.PartTwo.J2Residue.C4725 CFSG.RankThree.PartTwo.J2Residue.H2S

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem mbLenOK : Nat.beq (List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) MB) 16 = true := by
  decide +kernel

theorem mbLen : MB.length = 16 := by
  rw [← listLen_eq]
  exact beq_true mbLenOK

theorem spLenOK : allN 3 (fun k => Nat.beq (List.rec (motive := fun _ => Nat) 0
    (fun _ _ ih => Nat.succ ih) (getL [] SP k)) 12) = true := by
  decide +kernel

theorem spLen : ∀ k < 3, (getL [] SP k).length = 12 := fun k hk => by
  rw [← listLen_eq]
  exact beq_true (CFSG.KS.PK.allN_iff.1 spLenOK k hk)

theorem spgLenOK : allN 5 (fun l => Nat.beq (List.rec (motive := fun _ => Nat) 0
    (fun _ _ ih => Nat.succ ih) (getL [] SPG l)) 12) = true := by
  decide +kernel

theorem spgLen : ∀ l < 5, (getL [] SPG l).length = 12 := fun l hl => by
  rw [← listLen_eq]
  exact beq_true (CFSG.KS.PK.allN_iff.1 spgLenOK l hl)

theorem rows_all : ∀ i < 384, rowOKf (rowsPack HR) repN LMP MTP SP i = true := by
  have hb : ∀ c < 12, cocBlk (32 * c) = true := by
    intro c hc
    interval_cases c
    · exact coc0
    · exact coc32
    · exact coc64
    · exact coc96
    · exact coc128
    · exact coc160
    · exact coc192
    · exact coc224
    · exact coc256
    · exact coc288
    · exact coc320
    · exact coc352
  intro i hi
  have h := hb (i / 32) (by omega)
  rw [cocBlk, strictB_eq, strictB_eq] at h
  have := CFSG.KC.Pack.allN_spec h (i % 32) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (32 * (i / 32)) (i % 32) = i := Nat.div_add_mod i 32
  rwa [e] at this

theorem norm_all : normK (rowsPack HR) = true := by
  have h := normOK
  rwa [strictB_eq] at h

theorem tree_all : treeK (rowsPack HR) GP PP = true := by
  have h := treeOK
  rwa [strictB_eq] at h

theorem free_all : freeK (rowsPack HR) h2Free = true := by
  have h := freeOK
  rwa [strictB_eq] at h

theorem rel_all : ∀ k < 3, relK (rowsPack HR) repN LMP BR SP DEPA k = true := by
  have h := relOK
  rw [strictB_eq, strictB_eq] at h
  exact CFSG.KC.Pack.allN_spec h

theorem phv_all : phvK (rowsPack HR) CQ PHI SPG NL PHV = true := by
  have h := phvOK
  rwa [strictB_eq] at h

theorem phi_all : ∀ l < 5, phiK MTP RS CQ PHI NL l = true := by
  intro l hl
  interval_cases l
  · exact phiOK0
  · exact phiOK1
  · exact phiOK2
  · exact phiOK3
  · exact phiOK4

theorem mask_all : ∀ j < 16, maskBlk YC MTP LMP GP PP CKB MB j = true := by
  intro j hj
  interval_cases j
  · exact mask0
  · exact mask1
  · exact mask2
  · exact mask3
  · exact mask4
  · exact mask5
  · exact mask6
  · exact mask7
  · exact mask8
  · exact mask9
  · exact mask10
  · exact mask11
  · exact mask12
  · exact mask13
  · exact mask14
  · exact mask15

theorem ech_all : ∀ i < 6, echChunk MB ST KS i = true := by
  intro i hi
  interval_cases i
  · exact ech0
  · exact ech1
  · exact ech2
  · exact ech3
  · exact ech4
  · exact ech5

theorem NL_get (l : ℕ) (hl : l < 5) : getL 0 NL l = 2 ∧ offL NL l = 2 * l := by
  interval_cases l <;> exact ⟨by decide, by decide⟩

theorem letters_eq : Nat.beq CertificateChecks.KernelJ2Cover.ALP (CertificateChecks.KernelJ2Cover.PA.S 0) &&
    Nat.beq CertificateChecks.KernelJ2Cover.BEP (CertificateChecks.KernelJ2Cover.PA.S 1) = true := by
  quickRfl

open CFSG.KS CFSG.KS.Raw CFSG.KS.Prim in
theorem wordK_eq : ∀ w : List ℕ, wordK CertificateChecks.KernelJ2Cover.ALP
    CertificateChecks.KernelJ2Cover.BEP w = CertificateChecks.KernelJ2Cover.wordP w := by
  have h := letters_eq
  rw [Bool.and_eq_true] at h
  have hA := Nat.eq_of_beq_eq_true h.1
  have hB := Nat.eq_of_beq_eq_true h.2
  intro w
  induction w with
  | nil => rfl
  | cons k w ih =>
    have e : wordK CertificateChecks.KernelJ2Cover.ALP CertificateChecks.KernelJ2Cover.BEP (k :: w) =
        pcomp 315 9 511 (nIf(Nat.beq k 0, CertificateChecks.KernelJ2Cover.ALP,
          CertificateChecks.KernelJ2Cover.BEP))
          (wordK CertificateChecks.KernelJ2Cover.ALP CertificateChecks.KernelJ2Cover.BEP w) := rfl
    rw [e, ih, hA, hB]
    rfl


open CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
  CFSG.EvenSmallLie.Child3 CFSG.KC.Child3 in
theorem conj_bridge (w : List ℕ) (x y : ℕ) (hx : x < 128) (hy : y < 128)
    (h : Nat.beq (pcomp 315 9 511 (wordK CertificateChecks.KernelJ2Cover.ALP
      CertificateChecks.KernelJ2Cover.BEP w) (CertificateChecks.KernelJ2Cover.ELT x))
      (pcomp 315 9 511 (CertificateChecks.KernelJ2Cover.ELT y) (wordK CertificateChecks.KernelJ2Cover.ALP
        CertificateChecks.KernelJ2Cover.BEP w)) = true) :
    wordP w * incl (elt x) = incl (elt y) * wordP w := by
  rw [wordK_eq] at h
  have e := Nat.eq_of_beq_eq_true h
  have h1 := rep_compA (rep_wordArr w) (rep_eltArrs hx)
  have h2 := rep_compA (rep_eltArrs hy) (rep_wordArr w)
  rw [CertificateChecks.KernelJ2Cover.wordArr_eq, CertificateChecks.KernelJ2Cover.eltArrs_eq x hx,
    compA_unpackN (CertificateChecks.KernelJ2Cover.wordP_canon w)
      (CertificateChecks.KernelJ2Cover.eltT_canon x hx)] at h1
  rw [CertificateChecks.KernelJ2Cover.wordArr_eq, CertificateChecks.KernelJ2Cover.eltArrs_eq y hy,
    compA_unpackN (CertificateChecks.KernelJ2Cover.eltT_canon y hy)
      (CertificateChecks.KernelJ2Cover.wordP_canon w)] at h2
  have e' : pcomp 315 9 (mask 9) (CertificateChecks.KernelJ2Cover.wordP w)
      (CertificateChecks.KernelJ2Cover.ELT x) = pcomp 315 9 (mask 9)
      (CertificateChecks.KernelJ2Cover.ELT y) (CertificateChecks.KernelJ2Cover.wordP w) := e
  rw [e'] at h1
  have := h1.unique h2
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_wordP, incl_coe, incl_coe]
  exact this

theorem mem_cellsAt {l m : ℕ} {e : ↥S × ↥S × ↥S × ↥S × (V12 →ₗ[ZMod 2] ZMod 2)}
    (he : e ∈ cellsAt CQ PHI NL l m) : ∃ a ∈ getL [] CQ l, ∃ b ∈ getL [] CQ l,
      e.1 = elt (a % 128) ∧ e.2.1 = elt (a / 128) ∧ e.2.2.1 = elt (b % 128) ∧
        e.2.2.2.1 = elt (b / 128) := by
  simp only [cellsAt, List.mem_flatMap, List.mem_map, List.mem_range] at he
  obtain ⟨a, ha, b, hb, rfl⟩ := he
  have hm : ∀ {L : List ℕ} {i : ℕ}, i < L.length → L.getD i 0 ∈ L := fun hi => by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  exact ⟨_, hm ha, _, hm hb, rfl, rfl, rfl, rfl⟩

theorem res_cob_J2 (ρ : ↥P →* Module.End (ZMod 2) V12) (hρ : IsMRep ρ) (c : ↥P → ↥P → V12)
    (hc : IsNormCoc ρ c) :
    ∃ b : ↥S → V12, ∀ s t : ↥S, c (incl s) (incl t) = cob (rhoS ρ) b s t := by
  have hcj := conj_num conjOK conj_bridge
  have hI := (rel_num rel_all covOK dataOK spyOK spLen).1
  refine res_cob (H := Hc (rowsPack HR)) (F := fun i => h2Free.getD i 0) (IND := IND.toFinset)
    (g := fun m => wordP (getL [] CW (m / 2))) (L := fun m => cellsAt CQ PHI NL (m / 2) (m % 2))
    (M := fun m i => bitZ PHV (32 * m + i))
    (fun j hj => isNormCoc_Hc rows_all norm_all dataOK mtOK spyOK spLen hρ hj)
    (fun j hj => treeZero_Hc tree_all dataOK hj)
    (fun i hi j hj => coordF_Hc free_all hi hj)
    (ech_sound mask_all ech_all ksOK depthOK dataOK mtOK mbLen hρ)
    (fun i hi => Finset.mem_range.2 (hI i (List.mem_toFinset.1 hi)))
    (relation_Hc rows_all norm_all rel_all covOK dataOK mtOK spyOK spLen hρ)
    (fun m hm e he => ?_)
    (fun m hm => phi_sound phi_all rsOK dataOK mtOK hρ (m / 2) (by omega) (m % 2)
      (by rw [(NL_get (m / 2) (by omega)).1]; omega))
    (fun m hm i hi => ?_)
    (rank_num rankOK hI) hc
  · obtain ⟨a, ha, b, hb, h1, h2, h3, h4⟩ := mem_cellsAt he
    obtain ⟨-, -, ea⟩ := hcj (m / 2) (by omega) a ha
    obtain ⟨-, -, eb⟩ := hcj (m / 2) (by omega) b hb
    rw [h1, h2, h3, h4]
    exact ⟨eq_mul_inv_of_mul_eq ea.symm, eq_mul_inv_of_mul_eq eb.symm⟩
  · have := psi_sound phv_all spgOK spgLen rgOK (fun l hl e he => (hcj l hl e he).2.1) hρ (m / 2) (by omega) (m % 2)
      (by rw [(NL_get (m / 2) (by omega)).1]; omega) i hi
    rw [this, (NL_get (m / 2) (by omega)).2]
    congr 2
    omega

end CertificateChecks.J2H2

end
