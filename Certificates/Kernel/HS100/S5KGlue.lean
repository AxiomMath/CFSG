module

public import Certificates.Kernel.HS100.S5KChecks
public import Certificates.Kernel.HS100.S5OGlue
public import CFSG.Certificates.Kernel.PGrpMul
public import CFSG.Certificates.Kernel.MonsterB.Co2CountSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS100.S5K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum CFSG.KC.PGrp
open CFSG.EvenSporadicStandard.HSStd CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
open CFSG.RankThree.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer
open CertificateChecks.KernelHS100

theorem psLt : ∀ p ∈ s5Keys, p < 100 := by decide

theorem tab_eq {k : ℕ} (hk : k < 5) : s5Tab k = unpack 100 7 (F k) := by
  rw [s5Tab, F, CertificateChecks.KernelMisc.HS100.S0.ZX.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable3_sound CertificateChecks.KernelMisc.HS100.S0.ZX.all k hk

theorem z_eq : s5Z = unpack 100 7 Z := tab_eq (by norm_num)

theorem nums' : CS.ng = 4 ∧ CS.N = 1024 ∧ ∀ k < 4, CS.G k = F k := by
  have h := nums
  simp only [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1.1, Nat.eq_of_beq_eq_true h.1.2,
    fun k hk => Nat.eq_of_beq_eq_true (allN_spec h.2 k hk)⟩

theorem ppF {k : ℕ} (hk : k < 5) : PP 100 7 (F k) := pp_of_permB hw (allN_spec perm k hk)

theorem sgen_eq {k : ℕ} (hk : k < 4) : s5SGens[k]! = unpack 100 7 (F k) := by
  interval_cases k
  · exact tab_eq (by norm_num)
  · exact tab_eq (by norm_num)
  · exact tab_eq (by norm_num)
  · exact tab_eq (by norm_num)

theorem cs_gens : s5SGens.size = CS.ng ∧ ∀ k < CS.ng, s5SGens[k]! = unpack 100 7 (CS.G k) := by
  refine ⟨by rw [nums'.1]; rfl, fun k hk => ?_⟩
  rw [nums'.1] at hk
  rw [nums'.2.2 k hk]
  exact sgen_eq hk

theorem cs_perm : ∀ k < CS.ng, permOK 100 7 (mask 7) (100 * 7) (CS.G k)
    (pinvS 100 7 (mask 7) (CS.G k)) = true := by
  intro k hk
  rw [nums'.1] at hk
  rw [nums'.2.2 k hk]
  exact allN_spec perm k (by omega)

theorem keys' : keysSK 100 7 s5Keys CS.N CS.T CS.SK = true := keys

theorem cs_pts : s5SCert.pts = Array.ofFn (n := CS.N) fun i => unpack 100 7 (CS.T i.val) := by
  unfold s5SCert
  exact enumBfs_pts_base cs_gens.1 cs_gens.2 CS.ok psLt keys' (by rw [nums'.2.1]; norm_num)

theorem cs_enumOK : enumOK 100 s5SGens s5Keys s5SCert = true := by
  unfold s5SCert
  exact enumOK_of_bfsK_base cs_gens.1 cs_gens.2 cs_perm CS.ok psLt keys'
    (by rw [nums'.2.1]; norm_num)

theorem cs_size : s5SCert.pts.size = CS.N := by rw [cs_pts, Array.size_ofFn]

theorem cs_get : ∀ i < CS.N, s5SCert.pts[i]! = unpack 100 7 (CS.T i) := fun i hi => by
  rw [cs_pts, getElem!_pos _ i (by rw [Array.size_ofFn]; exact hi), Array.getElem_ofFn]

theorem ppCS {i : ℕ} (hi : i < CS.N) : PP 100 7 (CS.T i) := PP_pts CS.ok cs_perm i hi

theorem permCS {i : ℕ} (hi : i < CS.N) : permB 100 7 (CS.T i) = true := permB_of_pp (ppCS hi)

theorem memCS {i : ℕ} (hi : i < CS.N) :
    permOfArr 100 (unpack 100 7 (CS.T i)) ∈ Subgroup.closure (permsA 100 s5SGens) :=
  mem_of_pt hw psLt cs_enumOK cs_size cs_get hi

theorem zParts : rngK Z = true ∧ inHS Z = true ∧ Nat.beq Z (pidn 100 7) = false ∧
    Nat.beq (pm Z Z) (pidn 100 7) = true ∧ memK 1024 CS.T Z = true := by
  have h := S5K.z
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem permZ : permB 100 7 Z = true := allN_spec perm 4 (by norm_num)

theorem memZ : permOfArr 100 (unpack 100 7 Z) ∈ Subgroup.closure (permsA 100 s5SGens) :=
  mem_of_memK hw psLt cs_enumOK cs_size cs_get (by rw [nums'.2.1]; exact zParts.2.2.2.2)

theorem gensP' : allLt s5SGens.size
    (fun k => s5InP s5SGens[k]! || s5InP (compA 100 s5U s5SGens[k]!)) = true := by
  rw [allLt_iff]
  intro k hk
  have hk4 : k < 4 := hk
  have h := allN_spec gensP k hk4
  rw [sgen_eq hk4, s5U_eq, compO ppU (ppF (by omega))]
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h ⊢
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (inP_of h1 h2)
  · exact Or.inr (inP_of h1 h2)

theorem inP_pt {i : ℕ} (hi : i < 1024) :
    s5InP (unpack 100 7 (CS.T i)) = inHS (CS.T i) := by
  have hr := allN_spec os i hi
  unfold osOne at hr
  rw [Bool.and_eq_true] at hr
  cases hs : inHS (CS.T i)
  · exact notP_of hr.1 hs
  · exact inP_of hr.1 hs

theorem iN {i : ℕ} (hi : i < 1024) : i < CS.N := by rw [nums'.2.1]; exact hi

theorem osAll : (s5SCert.pts.toList.all fun x =>
    !s5InP x || eqA 100 (compA 100 s5Z x) (compA 100 x s5Z)) = true := by
  rw [cs_pts, pts_toList (N := CS.N) fun e => unpack 100 7 (CS.T e), List.all_map,
    List.all_eq_true]
  intro i hi
  have hi' : i < 1024 := by rw [← nums'.2.1]; exact List.mem_range.1 hi
  have h := allN_spec os i hi'
  unfold osOne at h
  rw [Bool.and_eq_true] at h
  simp only [Function.comp_apply]
  rw [inP_pt hi', z_eq, eqA_keyCK hw psLt cs_enumOK permZ (permCS (iN hi')) (permCS (iN hi'))
    permZ memZ (memCS (iN hi')) (memCS (iN hi')) memZ, Bool.or_comm]
  exact h.2

theorem out1_eq {i : ℕ} (hi : i < 1024) : s5Out1 (unpack 100 7 (CS.T i)) = out1 i := by
  unfold s5Out1 out1
  rw [inP_pt hi, idA_eq hw, eqA_keyCK_keyK hw psLt cs_enumOK (permCS (iN hi)) (permCS (iN hi))
    (permB_of_pp (PP.id hw)) (memCS (iN hi)) (memCS (iN hi)) (mem_id hw), Bool.and_comm]
  rfl

theorem outZ_eq {i : ℕ} (hi : i < 1024) : s5OutZ (unpack 100 7 (CS.T i)) = outZ i := by
  unfold s5OutZ outZ
  rw [inP_pt hi, z_eq, eqA_keyCK_keyK hw psLt cs_enumOK (permCS (iN hi)) (permCS (iN hi))
    permZ (memCS (iN hi)) (memCS (iN hi)) memZ, Bool.and_comm]
  rfl

theorem cnts' : CFSG.KC.Co2Mem.cntK 1024 out1 = 104 ∧ CFSG.KC.Co2Mem.cntK 1024 outZ = 40 := by
  have h := cnts
  rw [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem size1024 : s5SCert.pts.size = 1024 := by rw [cs_size, nums'.2.1]

theorem cnt1 : s5Cnt1 = 104 := by
  unfold s5Cnt1
  refine (CFSG.KC.Co2Mem.card_filter_fin s5SCert.pts.size
    (fun k => s5Out1 s5SCert.pts[k]! = true) out1 fun k hk => ?_).trans ?_
  · rw [size1024] at hk
    rw [cs_get k (iN hk), out1_eq hk]
  · rw [size1024]
    exact cnts'.1

theorem cntZ : s5CntZ = 40 := by
  unfold s5CntZ
  refine (CFSG.KC.Co2Mem.card_filter_fin s5SCert.pts.size
    (fun k => s5OutZ s5SCert.pts[k]! = true) outZ fun k hk => ?_).trans ?_
  · rw [size1024] at hk
    rw [cs_get k (iN hk), outZ_eq hk]
  · rw [size1024]
    exact cnts'.2

theorem s5SylowOK_true : s5SylowOK = true := by
  obtain ⟨zr, zh, zn, zz, -⟩ := zParts
  have p4 : PP 100 7 Z := ppF (by norm_num)
  have c1 : (s5SCert.pts.size == 1024) = true := by rw [size1024]; rfl
  have c2 : validA 100 s5Z = true := by rw [z_eq]; exact validA_unpack permZ
  have c3 : s5InP s5Z = true := by rw [z_eq]; exact inP_of zr zh
  have c4 : (!eqA 100 s5Z (idA 100)) = true := by
    rw [z_eq, idA_eq hw, eqO p4 (PP.id hw), zn]; rfl
  have c5 : eqA 100 (compA 100 s5Z s5Z) (idA 100) = true := by
    rw [z_eq, compO p4 p4, idA_eq hw, eqO (ppm p4 p4) (PP.id hw)]
    exact zz
  unfold s5SylowOK
  rw [cs_enumOK, c1, gensP', c2, c3, c4, c5, osAll, cnt1, cntZ]
  rfl

end CertificateChecks.KernelHS100.S5K

end
