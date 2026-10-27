module

public import Certificates.Kernel.HeLoc.FiveC0
public import CFSG.Certificates.Kernel.HeLoc.TreeSound
public import CFSG.Certificates.Kernel.HeLoc.HeFaith
public import CFSG.Certificates.Kernel.SporSch.PairHeCntSound
public import CFSG.Certificates.Kernel.Misc.PermClosSound
public import Certificates.Data.GrSLitL34HeldCenterCheck
public import CFSG.Sporadic.Schreier.PairHeClassesBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHeLoc.Five

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.HeLoc
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier CFSG.RankThree.Native CFSG.RankThree.PartOne
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch
open CFSG.KC.Misc.Clos (allN_iff forall_of_chunks)

theorem unpackGet {p x : Nat} (hx : x < 8330) : (unpack 8330 14 p)[x]! = pg 14 (mask 14) p x := by
  rw [unpack, getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

theorem repF_of_rep {p : Nat} {u : Equiv.Perm (Fin 8330)} (h : Rep 8330 (unpack 8330 14 p) u) :
    RepF 8330 (pg 14 (mask 14) p) u := fun x hx => by
  rw [← unpackGet hx]
  exact h ⟨x, hx⟩

theorem arr_eq (j : Nat) (hj : j < 13) : heFiveArr j = unpack 8330 14 (FH.F j) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound FH.all j hj
  rw [← FH.eq] at h
  rw [heFiveArr]
  exact h

theorem gens_lit : heFiveC0Gens =
    #[unpack 8330 14 (G 0), unpack 8330 14 (G 1), unpack 8330 14 (G 2)] := by
  rw [heFiveC0Gens, arr_eq 8 (by norm_num), arr_eq 9 (by norm_num), arr_eq 10 (by norm_num)]
  rfl

theorem gens_eq (k : Nat) (hk : k < 3) : heFiveC0Gens[k]! = unpack 8330 14 (G k) := by
  rw [gens_lit]
  interval_cases k <;> rfl

@[expose] noncomputable def gp (k : Nat) : Equiv.Perm (Fin 8330) :=
  permOfArr 8330 (unpack 8330 14 (G k))

theorem rep_gp (k : Nat) (hk : k < 3) : Rep 8330 (unpack 8330 14 (G k)) (gp k) :=
  (rep_permOfArr (invEqK_sound (allN_spec kPerm k hk)).2).1

theorem hgs : ∀ k < 3, Rep 8330 heFiveC0Gens[k]! (gp k) := fun k hk => by
  rw [gens_eq k hk]
  exact rep_gp k hk

theorem hg : ∀ k < 3, RepF 8330 (g k) (gp k) := fun k hk => repF_of_rep (rep_gp k hk)

noncomputable abbrev El (Fv : Nat) : Equiv.Perm (Fin 8330) :=
  nfElt 8330 heStrongArrs heBase.toArray (nfArr 5 Fv)

theorem El_rep {Fv : Nat} (hF : nfValidK 5 HeC.LR Fv = true) : RepF 8330 (HeTc.nfp Fv) (El Fv) :=
  (nfPtT_sound HeTc.tc hF).2

theorem El_mem {Fv : Nat} (hF : nfValidK 5 HeC.LR Fv = true) :
    El Fv ∈ heP := by
  rw [heP_eq_originalSubgroup]
  exact nfElt_mem heChainArrays (chainCheckFacts heChain_check.1) heChain_valid.1
    (nfPtT_sound HeTc.tc hF).1

theorem hF (j : Nat) (hj : j < 3) : nfValidK 5 HeC.LR (F j) = true := allN_spec kNF j hj

theorem bind_all : ∀ x < 8330, bindAt x = true := by
  have h := forall_of_chunks 833 10 bindAt fun c hc => by
    interval_cases c
    exacts [kB0, kB1, kB2, kB3, kB4, kB5, kB6, kB7, kB8, kB9]
  exact fun x hx => h x (by omega)

theorem bind_parts (x : Nat) (hx : x < 8330) :
    bind5At 8330 14 HeTb.NR HeTb.NR HeTb.LT HeTb.PT (F 0) (G 0) x = true ∧
      bind5At 8330 14 HeTb.NR HeTb.NR HeTb.LT HeTb.PT (F 1) (G 2) x = true ∧
      g 1 (uF x) = HeTc.nfp (F 2) x := by
  have h := bind_all x hx
  unfold bindAt at h
  rw [bAnd_iff, bAnd_iff] at h
  exact ⟨h.1, h.2.1, Nat.eq_of_beq_eq_true h.2.2⟩

theorem gp0 : gp 0 = El (F 0) :=
  (hg 0 (by norm_num)).unique (bind5_spec HeTc.tc (hF 0 (by norm_num))
    fun x hx => (bind_parts x hx).1)

theorem gp2 : gp 2 = El (F 1) :=
  (hg 2 (by norm_num)).unique (bind5_spec HeTc.tc (hF 1 (by norm_num))
    fun x hx => (bind_parts x hx).2.1)

theorem R_eq : heAutRArr = unpack 8330 14 (AR.F 0) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound AR.all 0 (by norm_num)
  rw [← AR.eq, Nat.mul_zero] at h
  rw [heAutRArr]
  exact h

theorem hU : RepF 8330 uF heAutU := by
  have hR : RepF 8330 (pg 14 (mask 14) (AR.F 0)) heAutR := by
    have h := rep_heAutR
    rw [R_eq] at h
    exact repF_of_rep h
  exact RepF.powF hR 5

theorem gp1u : gp 1 * heAutU = El (F 2) :=
  ((hg 1 (by norm_num)).comp hU).unique fun x hx =>
    ((bind_parts x hx).2.2).trans (El_rep (hF 2 (by norm_num)) x hx)

theorem gp_mem :
    ∀ k < 3, gp k ∈ heAutGroup := by
  intro k hk
  interval_cases k
  · rw [gp0]
    exact heP_le_heAutGroup (El_mem (hF 0 (by norm_num)))
  · have e : gp 1 = El (F 2) * heAutU⁻¹ := by rw [← gp1u, mul_inv_cancel_right]
    rw [e]
    exact heAutGroup.mul_mem (heP_le_heAutGroup (El_mem (hF 2 (by norm_num))))
      (heAutGroup.inv_mem heAutU_mem_heAutGroup)
  · rw [gp2]
    exact heP_le_heAutGroup (El_mem (hF 1 (by norm_num)))

theorem gp_par :
    ∀ k < 3, (gp k ∈ heP ↔ q k = 0) := by
  intro k hk
  interval_cases k
  · exact iff_of_true (by rw [gp0]; exact El_mem (hF 0 (by norm_num))) rfl
  · refine iff_of_false (fun h => heAutU_not_mem ?_) (by decide)
    have e : heAutU = (gp 1)⁻¹ * El (F 2) := by rw [← gp1u, inv_mul_cancel_left]
    rw [e]
    exact heP.mul_mem (heP.inv_mem h) (El_mem (hF 2 (by norm_num)))
  · exact iff_of_true (by rw [gp2]; exact El_mem (hF 1 (by norm_num))) rfl

theorem q_lt : ∀ k < 3, q k < 2 := by
  intro k hk
  interval_cases k <;> decide

theorem bs_lt : ∀ b ∈ bs, b < 8330 := by decide

theorem faithful :
    ∀ x ∈ heAutGroup, ∀ y ∈ heAutGroup, (x ∈ heP ↔ y ∈ heP) →
      (∀ b (hb : b ∈ bs), (x ⟨b, bs_lt b hb⟩ : Nat) = y ⟨b, bs_lt b hb⟩) → x = y := by
  intro x hx y hy hxy hb
  refine he_eq_of_base hx hy hxy fun b hb5 => Fin.ext ?_
  have hm : (b : Nat) ∈ bs := by
    simp only [bs, List.mem_cons, List.not_mem_nil, or_false]
    omega
  exact hb b hm

theorem tree : TreeOK 3 600 C0.P C0.L := treeOK_of fun i hi h0 => by
  have h := allN_spec kTree i hi
  rwa [beq_zero_false h0] at h

theorem edges :
    ∀ i < 600, ∀ k < 3, E i k < 600 ∧
      treeArr 8330 heFiveC0Gens C0.P C0.L (E i k) =
        compA 8330 heFiveC0Gens[k]! (treeArr 8330 heFiveC0Gens C0.P C0.L i) :=
  edges_of_edgeAtK tree hg hgs (fun a ha b hb => he_mul_mem_iff ha hb) gp_mem gp_par q_lt bs_lt
    faithful fun i hi => allN_spec kEdge i hi

theorem keys_lt : ∀ p ∈ heFiveKeys, p < 8330 := by decide

theorem pts_eq :
    heFiveC0Cert.pts = Array.ofFn (n := 600) fun i => treeArr 8330 heFiveC0Gens C0.P C0.L i.val := by
  have hk := keys_inj_of_sortAtK (key := key) fun j hj => allN_spec kSort j hj
  refine enumBfs_tree tree hgs (by rfl) (by norm_num) (by norm_num) ?_ edges kReplay
  intro a ha b hb e
  rw [keyA_treeArr tree hg hgs keys_lt ha, keyA_treeArr tree hg hgs keys_lt hb] at e
  exact hk a ha b hb e

theorem noFour :
    CFSG.ComponentClassification.GrSLit.L34HeldCenter.heFiveNoFourOK = true := by
  unfold CFSG.ComponentClassification.GrSLit.L34HeldCenter.heFiveNoFourOK
  rw [pts_eq, allLt_iff]
  intro i hi
  rw [Array.size_ofFn] at hi
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  set p := treeArr 8330 heFiveC0Gens C0.P C0.L i
  set u := treePerm gp C0.P C0.L i
  have hp : Rep 8330 p u := rep_treeArr tree hgs i hi
  have hR : RepF 8330 (tv i) u := repF_trV tree hg 600 i hi.le hi
  obtain ⟨huR, huP, -⟩ := trQ_spec tree (fun a ha b hb => he_mul_mem_iff ha hb) gp_mem gp_par q_lt
    600 i hi.le hi
  have hu2 : u * u ∈ heP := he_sq_mem huR
  have hu4 : u * u * (u * u) ∈ heP := heP.mul_mem hu2 hu2
  have hH := he_baseFaithful
  have hbs : ∀ b ∈ PairHe.bs, b < 8330 := he_bs_lt
  have e4 : u ^ 4 = u * u * (u * u) := by rw [show (4 : Nat) = 2 + 2 from rfl, pow_add, sq]
  have e2 : u ^ 2 = u * u := sq u
  have hf4 : eqOnL bs (powF (tv i) 4) (fun x => x) = true ↔ u * u * (u * u) = 1 := by
    rw [← e4]
    refine fixL_iff hH hbs (RepF.powF hR 4) ?_
    rw [e4, ← heP_eq_originalSubgroup]
    exact hu4
  have hf2 : eqOnL bs (powF (tv i) 2) (fun x => x) = true ↔ u * u = 1 := by
    rw [← e2]
    refine fixL_iff hH hbs (RepF.powF hR 2) ?_
    rw [e2, ← heP_eq_originalSubgroup]
    exact hu2
  have h4 := eqA_iff (rep_compA (rep_compA hp hp) (rep_compA hp hp)) rep_idA
  have h2 := eqA_iff (rep_compA hp hp) rep_idA
  have hs := mem_heP_iff_siftA hp
  have hfour := allN_spec kFour i hi
  unfold fourAt at hfour
  rw [Bool.or_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.not_eq_true']
  by_cases a4 : u * u * (u * u) = 1
  · by_cases a2 : u * u = 1
    · exact Or.inl (Or.inr (h2.2 a2))
    · right
      rw [show heLevels = rawLevels 8330 heStrongArrs heBase.toArray from rfl,
        Bool.eq_false_iff]
      intro hsf
      have hP := hs.1 hsf
      rw [hf4.2 a4, Bool.eq_false_iff.2 (fun h => a2 (hf2.1 h))] at hfour
      have hq := Nat.eq_of_beq_eq_true hfour
      rw [huP] at hP
      omega
  · exact Or.inl (Or.inl (Bool.eq_false_iff.2 fun h => a4 (h4.1 h)))

end CertificateChecks.KernelHeLoc.Five

end
