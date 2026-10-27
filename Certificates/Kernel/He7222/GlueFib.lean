module

public import Certificates.Kernel.He7222.GlueK
public import Certificates.Kernel.He7222.GlueGood
public import Certificates.Kernel.He7222.FtK
public import CFSG.Certificates.Kernel.He7222.FibSound
public import CFSG.Certificates.Kernel.He7222.CoverGrp
import Mathlib.Data.List.Forall2
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.OrbRow.LevelSound
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.Loops

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHe7222

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.OrbRow CFSG.KC.HeChain CFSG.KS.Raw.Orb
  CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.KD.He7222 CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.He
  CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier CFSG.Monster.B.Co2.Native
  CertificateChecks.KernelLC.HeFix CertificateChecks.KernelHe7223
  CertificateChecks.KernelSchreierFam.He725 CFSG.KS.PF

theorem allBlk_of' {b : ℕ} {f : ℕ → Bool} : ∀ {len : ℕ},
    (∀ l < len, f (Nat.add b l) = true) → allBlk b f len = true
  | 0, _ => rfl
  | len + 1, h => by
    change Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) = true
    rw [h len (by omega)]
    exact allBlk_of' fun l hl => h l (by omega)

theorem allN5_of {f : ℕ → Bool} (h : ∀ k < 5, f k = true) : allN 5 f = true := by
  change Bool.rec (motive := fun _ => Bool) false true (allBlk 0 f 5) = true
  rw [allBlk_of' fun l hl => by
    have e : Nat.add 0 l = l := Nat.zero_add l
    rw [e]
    exact h l hl]

theorem lenLN_eq : ∀ L : List (List ℕ), lenLN L = L.length
  | [] => rfl
  | _ :: L => by
    change Nat.succ (lenLN L) = _
    rw [lenLN_eq L]
    rfl

theorem ftOK_spec {KTs : List (List ℕ)} : ∀ {FT : List (List ℕ)}, ftOK KTs FT = true →
    ∀ kt ∈ FT, tupOK KTs kt = true
  | [], _, kt, hk => absurd hk List.not_mem_nil
  | t :: FT, h, kt, hk => by
    have h' : bAnd(tupOK KTs t, ftOK KTs FT) = true := h
    rw [bAnd_iff] at h'
    rcases List.mem_cons.1 hk with rfl | hk
    · exact h'.1
    · exact ftOK_spec h'.2 kt hk

theorem frOK_spec {nt : ℕ} : ∀ {FR : List (List ℕ)}, frOK nt FR = true →
    ∀ rec ∈ FR, getS rec 1 < nt
  | [], _, rec, hr => absurd hr List.not_mem_nil
  | t :: FR, h, rec, hr => by
    have h' : bAnd(Nat.blt (getS t 1) nt, frOK nt FR) = true := h
    rw [bAnd_iff, Nat.blt_eq] at h'
    rcases List.mem_cons.1 hr with rfl | hr
    · exact h'.1
    · exact frOK_spec h'.2 rec hr

theorem forall₂_range {KTs : List (List ℕ)} {g : ℕ → ℕ}
    (hg : ∀ i < KTs.length, g i ∈ KTs.getD i []) :
    List.Forall₂ (· ∈ ·) ((List.range KTs.length).map g) KTs := by
  induction KTs generalizing g with
  | nil => exact List.Forall₂.nil
  | cons T KTs ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    refine List.Forall₂.cons (hg 0 (by simp)) ?_
    exact ih fun i hi => hg (i + 1) (by simpa using hi)

theorem eq_of_pts5 {g g' : Equiv.Perm (Fin 8330)} (hg : g ∈ heP)
    (hg' : g' ∈ heP) (h : ∀ p : Fin 8330, (p : ℕ) < 5 → (g p : ℕ) = g' p) : g = g' := by
  refine CFSG.KC.WordPts.eq_of_pts baseFaithful_heP hg hg' fun p hp => Fin.ext (h p ?_)
  simp only [bs, List.mem_cons, List.not_mem_nil, or_false] at hp
  omega

theorem scan_fibre
    {τ h s : Equiv.Perm (Fin 8330)} {τP hPk hIk : ℕ}
    (hτP : PRep 8330 14 τP τ) (hτ : τ ∈ heP) (hhP : PRep 8330 14 hPk h)
    (hhI : PRep 8330 14 hIk h⁻¹) (hh : h ∈ heP) (hhs : h * τ = s * h)
    (hsC : s ∈ centralizerIn heP τ)
    {Ts TIs : List (List ℕ)} (hTI : TIs.length = Ts.length)
    (hrep : ∀ t < Ts.length, ∀ j < (Ts.getD t []).length,
      recP 8330 14 ((Ts.getD t []).getD j 0) ∈ centralizerIn heP τ ∧
      PRep 8330 14 ((Ts.getD t []).getD j 0) (recP 8330 14 ((Ts.getD t []).getD j 0)))
    (hshr : ∀ t < Ts.length, ∀ j < (Ts.getD t []).length,
      (Ts.getD t []).getD j 0 >>> (8330 * 14) = 0)
    (hinv : ∀ t < Ts.length,
      invLK 8330 14 (mask 14) (pidn 8330 14) (Ts.getD t []) (TIs.getD t []) = true)
    {rs : List ℕ} (hrs : ∀ p : Fin 8330, evK 14 (mask 14) rs p = s p)
    {KC : List (List ℕ)} {keys : List ℕ} (hcls : clsK 14 (mask 14) Ts TIs rs KC keys = true)
    {KTs : List (List ℕ)} {Lk : ℕ} (hKL : KTs.length = Lk)
    (hKent : ∀ i < Lk, ∀ k < (KTs.getD i []).length,
      recP 8330 14 ((KTs.getD i []).getD k 0) ∈ centralizerIn heP τ ⊓ Subgroup.centralizer {s} ∧
      PRep 8330 14 ((KTs.getD i []).getD k 0) (recP 8330 14 ((KTs.getD i []).getD k 0)))
    (hKfac : ∀ g ∈ centralizerIn heP τ ⊓ Subgroup.centralizer {s}, ∃ f : ℕ → ℕ,
      (∀ i < Lk, f i < (KTs.getD i []).length) ∧
      g = ((List.range Lk).map fun i => recP 8330 14 ((KTs.getD i []).getD (f i) 0)).prod)
    (hKcomp : ∀ z ∈ centralizerIn heP τ, ∃ pos < KC.length,
      (tupP Ts (KC.getD pos []))⁻¹ * z ∈ centralizerIn heP τ ⊓ Subgroup.centralizer {s})
    {Sv : List ℕ} (hsv : svK 14 (mask 14) Ts TIs rs hPk hIk τP KC Sv = true)
    {XR : List ℕ} {SR : List (List ℕ)}
    (hsr : srK 14 (mask 14) Ts TIs KTs rs hPk hIk (lenS XR) KC XR Sv SR = true)
    (hxr : ∀ r < XR.length, XR.getD r 0 < KC.length)
    (hfib : ∀ r < XR.length, ∃ FR FT GD : List (List ℕ),
      fibK 14 (mask 14) KTs KTs.reverse (hPk :: stkK Ts (KC.getD (XR.getD r 0) [])) FR FT = true ∧
      ftOK KTs FT = true ∧ frOK (lenLN FT) FR = true ∧
      goodLK 14 (mask 14) KTs (hPk :: stkK Ts (KC.getD (XR.getD r 0) [])) τP LU LUI DW R5 R7 FT GD =
        true) :
    ∀ z ∈ centralizerIn heP τ, HConcl τ (h * z) := by
  intro z hz
  set C := centralizerIn heP τ with hCdef
  set K := C ⊓ Subgroup.centralizer {s} with hKdef
  have hKC : K ≤ C := inf_le_left
  have hCP : C ≤ heP := inf_le_left
  have hs' : s = h * τ * h⁻¹ := by rw [hhs, mul_inv_cancel_right]
  have hsP : s ∈ heP := hCP hsC
  obtain ⟨hlenK, hallK⟩ := clsK_sound hcls
  set rec : ℕ → ℕ → Equiv.Perm (Fin 8330) := fun t j => recP 8330 14 ((Ts.getD t []).getD j 0)
    with hrecdef
  have hmem : ∀ pos < KC.length, tupP Ts (KC.getD pos []) ∈ C ∧
      StkRep 8330 14 (stkK Ts (KC.getD pos [])) (tupL rec Ts.length (KC.getD pos [])) ∧
      ∀ p : Fin 8330,
      cjEv 14 (mask 14) (stkK Ts (KC.getD pos [])) rs (stkIK TIs (KC.getD pos []) []) p =
        (tupP Ts (KC.getD pos []) * s * (tupP Ts (KC.getD pos []))⁻¹) p := by
    intro pos hpos
    obtain ⟨htup, -⟩ := hallK pos hpos
    set ix := KC.getD pos [] with hix
    obtain ⟨hixl, hixb⟩ := tupOK_spec htup
    have hst := stkK_rep (n := 8330) (w := 14) rec htup (fun t ht j hj => (hrep t ht j hj).2)
    set cl := tupL rec Ts.length ix with hcl
    have hinvr : ∀ t < TIs.length, PRep 8330 14 ((TIs.getD t []).getD (ix.getD t 0) 0)
        ((fun t j => (rec t j)⁻¹) t (ix.getD t 0)) := by
      intro t ht
      have ht' : t < Ts.length := by omega
      obtain ⟨-, hi2⟩ := invLK_sound (hinv t ht')
      have hj := hixb t ht'
      exact invK_rep (by norm_num) (by norm_num) (hi2 _ hj) (hrep t ht' _ hj).2 (hshr t ht' _ hj)
    have hsti := stkIK_rep (n := 8330) (w := 14) (fun t j => (rec t j)⁻¹) (acc := [])
      (accg := []) (by omega) hinvr List.Forall₂.nil
    rw [List.append_nil, hTI] at hsti
    have hci : (tupL (fun t j => (rec t j)⁻¹) Ts.length ix).reverse.prod = cl.prod⁻¹ := by
      rw [hcl, List.prod_inv_reverse]
      simp only [tupL, List.map_map]
      rfl
    have hcP : cl.prod ∈ C := by
      refine Subgroup.list_prod_mem (K := C) fun g hg => ?_
      simp only [hcl, tupL, List.mem_map, List.mem_range] at hg
      obtain ⟨t, ht, rfl⟩ := hg
      exact (hrep t ht _ (hixb t ht)).1
    refine ⟨hcP, hst, fun p => ?_⟩
    change evK 14 (mask 14) _ (evK 14 (mask 14) rs (evK 14 (mask 14) _ p)) = _
    rw [evK_rep hsti p, hci, hrs, evK_rep hst]
    simp only [Equiv.Perm.mul_apply]
    rfl
  set recK : ℕ → ℕ → Equiv.Perm (Fin 8330) :=
    fun t j => recP 8330 14 ((KTs.getD t []).getD j 0) with hrecK
  have hktup : ∀ kt, tupOK KTs kt = true →
      StkRep 8330 14 (stkK KTs kt) (tupL recK KTs.length kt) ∧
      (tupL recK KTs.length kt).prod ∈ K := by
    intro kt hkt
    obtain ⟨-, hixb⟩ := tupOK_spec hkt
    refine ⟨stkK_rep (n := 8330) (w := 14) recK hkt
      (fun t ht j hj => (hKent t (by omega) j hj).2), ?_⟩
    refine Subgroup.list_prod_mem (K := K) fun g hg => ?_
    simp only [tupL, List.mem_map, List.mem_range] at hg
    obtain ⟨t, ht, rfl⟩ := hg
    exact (hKent t (by omega) _ (hixb t ht)).1
  intro hmove he hcomm
  have hzτ := (mem_centralizerIn.1 hz).2
  have hzP := hCP hz
  have hyP : h * z ∈ heP := heP.mul_mem hh hzP
  have hyτ : h * z * τ * (h * z)⁻¹ = s := by
    calc h * z * τ * (h * z)⁻¹ = h * (z * τ) * z⁻¹ * h⁻¹ := by group
      _ = h * τ * h⁻¹ := by rw [hzτ]; group
      _ = s := hs'.symm
  obtain ⟨pos, hpos, hcz⟩ := hKcomp z hz
  obtain ⟨hcC, hcS, hcev⟩ := hmem pos hpos
  set c := tupP Ts (KC.getD pos []) with hcdef
  have hcz' := Subgroup.mem_centralizer_singleton_iff.1 (inf_le_right (a := C) hcz)
  have hx : z * s * z⁻¹ = c * s * c⁻¹ := by
    calc z * s * z⁻¹ = c * (c⁻¹ * z * s) * (c⁻¹ * z)⁻¹ * c⁻¹ := by group
      _ = c * (s * (c⁻¹ * z)) * (c⁻¹ * z)⁻¹ * c⁻¹ := by rw [hcz']
      _ = c * s * c⁻¹ := by group
  have hys : h * z * s * (h * z)⁻¹ = h * (c * s * c⁻¹) * h⁻¹ := by
    rw [← hx]
    group
  have h2 := hcomm 2
  have hy2 : (h * z) ^ 2 * τ * ((h * z) ^ 2)⁻¹ = h * z * s * (h * z)⁻¹ := by
    rw [← hyτ, sq]
    group
  rw [hy2, hys] at h2
  have hxτ : c * s * c⁻¹ * (h⁻¹ * τ * h) = h⁻¹ * τ * h * (c * s * c⁻¹) := by
    calc c * s * c⁻¹ * (h⁻¹ * τ * h) =
        h⁻¹ * (h * (c * s * c⁻¹) * h⁻¹ * τ) * h := by group
      _ = h⁻¹ * (τ * (h * (c * s * c⁻¹) * h⁻¹)) * h := by rw [h2]
      _ = h⁻¹ * τ * h * (c * s * c⁻¹) := by group
  have hcm : cmK 14 (mask 14) (stkK Ts (KC.getD pos [])) rs (stkIK TIs (KC.getD pos []) [])
      hPk hIk τP = true := by
    unfold cmK
    apply allN5_of
    intro k hk
    obtain ⟨kF, hkF⟩ : ∃ kF : Fin 8330, (kF : ℕ) = k := ⟨⟨k, by omega⟩, rfl⟩
    rw [← hkF, hhP kF, hτP, hhI, hcev, hcev, hhP, hτP, hhI]
    have e := congrArg (fun g : Equiv.Perm (Fin 8330) => (g kF : ℕ)) hxτ
    simp only [Equiv.Perm.mul_apply] at e ⊢
    rw [e]
    exact Nat.beq_refl _
  have hpSv : pos ∈ Sv := svK_sound hsv pos hpos hcm
  obtain ⟨q, hq, hqp⟩ := List.getElem_of_mem hpSv
  obtain ⟨hSRl, hSR⟩ := srK_sound hsr
  obtain ⟨r, kt, -, hr, hkt, hse⟩ := hSR q (by omega)
  have hr' : r < XR.length := by
    rw [← lenS_eq]
    exact hr
  have hSvq : getS Sv q = pos := by
    rw [getS_eq, List.getD_eq_getElem _ _ hq, hqp]
  rw [hSvq, getLs_eq, getLs_eq, getS_eq] at hse
  obtain ⟨hkS, hkK⟩ := hktup kt hkt
  set kP := (tupL recK KTs.length kt).prod with hkPdef
  set xr := XR.getD r 0 with hxrdef
  obtain ⟨hcrC, hcrS, hcrev⟩ := hmem xr (hxr r hr')
  set cr := tupP Ts (KC.getD xr []) with hcrdef
  have hkC : kP ∈ C := hKC hkK
  have hkP : kP ∈ heP := hCP hkC
  have hks := Subgroup.mem_centralizer_singleton_iff.1 (inf_le_right (a := C) hkK)
  have hcP : c ∈ heP := hCP hcC
  have hcrP : cr ∈ heP := hCP hcrC
  have hxk : c * s * c⁻¹ * (h⁻¹ * kP * h) = h⁻¹ * kP * h * (cr * s * cr⁻¹) := by
    refine eq_of_pts5 (heP.mul_mem (heP.mul_mem (heP.mul_mem hcP hsP) (heP.inv_mem hcP))
      (heP.mul_mem (heP.mul_mem (heP.inv_mem hh) hkP) hh))
      (heP.mul_mem (heP.mul_mem (heP.mul_mem (heP.inv_mem hh) hkP) hh)
        (heP.mul_mem (heP.mul_mem hcrP hsP) (heP.inv_mem hcrP))) fun p hp => ?_
    have e := Nat.eq_of_beq_eq_true (allN_spec hse p hp)
    rw [hhP p, evK_rep hkS, hhI, hcev, hcrev, hhP, evK_rep hkS, hhI] at e
    simp only [Equiv.Perm.mul_apply] at e ⊢
    exact e
  refine hconcl_of_conj hkP (mem_centralizerIn.1 hkC).2 ?_ hmove he hcomm
  set y₂ := kP⁻¹ * (h * z) * kP with hy₂def
  have hy₂P : y₂ ∈ heP := heP.mul_mem (heP.mul_mem (heP.inv_mem hkP) hyP) hkP
  set z₂ := h⁻¹ * y₂ with hz₂def
  have hz₂P : z₂ ∈ heP := heP.mul_mem (heP.inv_mem hh) hy₂P
  have hkτ' : kP * τ * kP⁻¹ = τ := by rw [(mem_centralizerIn.1 hkC).2, mul_inv_cancel_right]
  have hks' : kP * s * kP⁻¹ = s := by rw [hks, mul_inv_cancel_right]
  have hz₂τ : z₂ * τ = τ * z₂ := by
    have e : z₂ * τ * z₂⁻¹ = τ := by
      calc z₂ * τ * z₂⁻¹ = h⁻¹ * kP⁻¹ * (h * z) * (kP * τ * kP⁻¹) * (h * z)⁻¹ * kP * h := by
            rw [hz₂def, hy₂def]
            group
        _ = h⁻¹ * (kP⁻¹ * (h * z * τ * (h * z)⁻¹) * kP) * h := by rw [hkτ']; group
        _ = h⁻¹ * (kP⁻¹ * s * kP) * h := by rw [hyτ]
        _ = h⁻¹ * (kP⁻¹ * (kP * s * kP⁻¹) * kP) * h := by rw [hks']
        _ = τ := by rw [hs']; group
    calc z₂ * τ = z₂ * τ * z₂⁻¹ * z₂ := by group
      _ = τ * z₂ := by rw [e]
  have hz₂C : z₂ ∈ C := mem_centralizerIn.2 ⟨hz₂P, hz₂τ⟩
  have hz₂s : z₂ * s * z₂⁻¹ = cr * s * cr⁻¹ := by
    calc z₂ * s * z₂⁻¹ = h⁻¹ * kP⁻¹ * (h * z) * (kP * s * kP⁻¹) * (h * z)⁻¹ * kP * h := by
          rw [hz₂def, hy₂def]
          group
      _ = h⁻¹ * (kP⁻¹ * (h * z * s * (h * z)⁻¹) * kP) * h := by rw [hks']; group
      _ = (h⁻¹ * kP * h)⁻¹ * (c * s * c⁻¹ * (h⁻¹ * kP * h)) := by rw [hys]; group
      _ = cr * s * cr⁻¹ := by rw [hxk]; group
  have hk3 : cr⁻¹ * z₂ ∈ K := by
    refine Subgroup.mem_inf.2 ⟨C.mul_mem (C.inv_mem hcrC) hz₂C,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc cr⁻¹ * z₂ * s = cr⁻¹ * (z₂ * s * z₂⁻¹) * z₂ := by group
      _ = s * (cr⁻¹ * z₂) := by rw [hz₂s]; group
  obtain ⟨f, hf, hfe⟩ := hKfac _ hk3
  set k₃ := ((List.range Lk).map fun i => recP 8330 14 ((KTs.getD i []).getD (f i) 0)).prod
    with hk₃def
  have hy₂e : y₂ = h * cr * k₃ := by
    rw [← hfe, hz₂def]
    group
  obtain ⟨FR, FT, GD, hfb, hft, hfr, hgd⟩ := hfib r hr'
  set gs := hPk :: stkK Ts (KC.getD xr []) with hgsdef
  have hgsR : StkRep 8330 14 gs (h :: tupL rec Ts.length (KC.getD xr [])) :=
    List.Forall₂.cons hhP hcrS
  set ts := (List.range Lk).map fun i => (KTs.getD i []).getD (f i) 0 with htsdef
  have htsR : StkRep 8330 14 ts ((List.range Lk).map fun i => recK i (f i)) :=
    stkRep_map fun i hi => (hKent i (List.mem_range.1 hi) (f i) (hf i (List.mem_range.1 hi))).2
  have hts : List.Forall₂ (· ∈ ·) ts KTs := by
    rw [htsdef, ← hKL]
    refine forall₂_range fun i hi => ?_
    rw [List.getD_eq_getElem (KTs.getD i []) 0 (hf i (by rw [← hKL]; exact hi))]
    exact List.getElem_mem _
  have hleaf := fibK_sound hfb ts.reverse (List.forall₂_reverse_iff.2 hts)
  rw [List.reverse_reverse] at hleaf
  have hF : ∀ x : Fin 8330, (fun p => evK 14 (mask 14) gs (evK 14 (mask 14) ts p)) x = y₂ x := by
    intro x
    change evK 14 (mask 14) gs (evK 14 (mask 14) ts x) = _
    rw [evK_rep htsR, evK_rep hgsR, hy₂e, List.prod_cons]
    rfl
  have hok : okK (fun p => evK 14 (mask 14) gs (evK 14 (mask 14) ts p)) = true := by
    obtain ⟨e, hes, hye⟩ := he
    have hy₂e' : y₂ ^ e = 1 := by
      rw [hy₂def, show kP⁻¹ * (h * z) * kP = kP⁻¹ * (h * z) * kP⁻¹⁻¹ by rw [inv_inv], conj_pow,
        hye, mul_one, mul_inv_cancel]
    refine okK_of_pow hes fun p hp => ?_
    obtain ⟨pF, hpF⟩ : ∃ pF : Fin 8330, (pF : ℕ) = p := ⟨⟨p, by omega⟩, rfl⟩
    rw [← hpF, iter_eq hF e pF, hy₂e']
    rfl
  obtain ⟨ri, t, k2, hmemR, hk2, hcy⟩ := hleaf hok
  have ht : t < FT.length := by
    have := frOK_spec hfr _ hmemR
    rw [lenLN_eq] at this
    exact this
  have hktt : tupOK KTs (FT.getD t []) = true :=
    ftOK_spec hft _ (by rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem _)
  obtain ⟨hk2S, hk2K⟩ := hktup k2 hk2
  obtain ⟨hktS, hktK⟩ := hktup _ hktt
  set k2P := (tupL recK KTs.length k2).prod with hk2Pdef
  set ktP := (tupL recK KTs.length (FT.getD t [])).prod with hktPdef
  have hk2P : k2P ∈ heP := hCP (hKC hk2K)
  have hktP : ktP ∈ heP := hCP (hKC hktK)
  set yt := h * cr * ktP with hytdef
  have hytP : yt ∈ heP := heP.mul_mem (heP.mul_mem hh hcrP) hktP
  rw [getLs_eq] at hcy
  have hyc : y₂ * k2P = k2P * yt := by
    refine eq_of_pts5 (heP.mul_mem hy₂P hk2P) (heP.mul_mem hk2P hytP) fun p hp => ?_
    have e := Nat.eq_of_beq_eq_true (allN_spec hcy p hp)
    rw [evK_rep hk2S, evK_rep htsR, evK_rep hgsR, evK_rep hktS, evK_rep hgsR, evK_rep hk2S] at e
    have e2 : (y₂ (k2P p) : ℕ) = (h * cr * k₃) (k2P p) := by rw [hy₂e]
    simp only [Equiv.Perm.mul_apply, List.prod_cons] at e e2 ⊢
    rw [e2]
    exact e
  have hyt : yt = k2P⁻¹ * y₂ * k2P := by
    rw [mul_assoc, hyc]
    group
  refine hconcl_of_conj hk2P (mem_centralizerIn.1 (hKC hk2K)).2 ?_
  rw [← hyt]
  obtain ⟨-, hgood⟩ := goodLK_sound hgd
  refine hconcl_of_goodK hτP hτ hytP (fun x => ?_) (hgood t ht)
  change evK 14 (mask 14) gs (evK 14 (mask 14) (stkK KTs (FT.getD t [])) x) = _
  rw [evK_rep hktS, evK_rep hgsR, List.prod_cons]
  rfl

end CertificateChecks.KernelHe7222

end
