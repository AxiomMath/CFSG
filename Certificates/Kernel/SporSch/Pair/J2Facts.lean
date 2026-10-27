module

public import Certificates.Kernel.SporSch.Pair.J2Check
public import CFSG.Certificates.Kernel.SporSch.Cnt3Proof
public import CFSG.Certificates.Kernel.SporSch.PairClProof

public section

namespace CertificateChecks.KernelSporSch.PJ2Facts

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.Schreier.PairJ2
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.PJ2W
open CertificateChecks.KernelSporSch.PJ2Check

private theorem sum_two {w₀ w₁ : List (Array Nat)}
    {C₀ C₁ : Array (Array Nat) × Array Nat × Array Nat} {s : Nat}
    (h : C₀.1.size + C₁.1.size = s) : ([(w₀, C₀), (w₁, C₁)].map fun c => c.2.1.size).sum = s := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  exact h

private theorem wsum_two {w₀ w₁ : List (Array Nat)}
    {C₀ C₁ : Array (Array Nat) × Array Nat × Array Nat} {f : List (Array Nat) → Nat}
    {n₀ n₁ t : Nat} (e₀ : f w₀ = n₀) (e₁ : f w₁ = n₁) (h : C₀.1.size * n₀ + C₁.1.size * n₁ = t) :
    ([(w₀, C₀), (w₁, C₁)].map fun c => c.2.1.size * f c.1).sum = t := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rw [e₀, e₁]
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem facts : (rawChainOK 315 ((j2StrongArrs ()).extract 0 2) (j2StrongArrs ()) baseArr (j2Words ()) 1 =
        true ∧ rawOrbitSizes 315 (j2StrongArrs ()) baseArr = [315, 160, 12])
    ∧ (ordB bs wA 2 = true ∧ ordB bs wB 3 = true ∧ ordB bs (patW wA wB [false, true]) 7 = true ∧
      ordB bs (patW wA wB commPat) 12 = true)
    ∧ (countW (fun w => ordB bs w 2) blocks [] = 2835 ∧
      countW (fun w => ordB bs w 3) blocks [] = 17360)
    ∧ ((∀ c ∈ cl, ordB bs c.1 2 = true) ∧
      (∀ c ∈ cl, closureOK levels bs gens gensInv c.1 c.2.1 c.2.2.1 c.2.2.2 = true) ∧
      keysDistinctNF 315 levels bs (cl.map fun c => c.2.1) = true ∧
      (cl.map fun c => c.2.1.size).sum = 2835)
    ∧ ((cl.map fun c => c.2.1.size *
      countW (fun y => ordB bs y 3 && condsOK bs c.1 y conds) blocks []).sum = 1209600) := by
  have srt := keysK_sound
    (cs := [(PJ2C.c0, nfKeyX 315 9 PJ2.LR PJ2.TR 3 bs PJ2C.XT0 76),
      (PJ2C.c1, nfKeyX 315 9 PJ2.LR PJ2.TR 3 bs PJ2C.XT1 76)]) (by decide) (by decide) PJ2C.hsrt
  have hD := nodup_of_strictInc_mergeSort srt
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hD
  have cl0 := ClP.closNF_proved (bs := bs) (rep := wA) PJ2.binds PJ2.perm PJ2.hl rfl hg rep0_eq ok0
    (List.nodup_append.1 hD).1
  have cl1 := ClP.closNF_proved (bs := bs) (rep := (List.replicate 6 (patW wA wB commPat)).flatten)
    PJ2.binds PJ2.perm PJ2.hl rfl hg rep1_eq ok1 (List.nodup_append.1 hD).2.1
  have n2 := cnt3_proved (bs := bs) (XP := RPnil) (conds := PairNil.noConds) PJ2.binds PJ2.perm
    PJ2.hl rfl canonNil hsz PJ2K2.hk
  have n30 := cnt3_proved (bs := bs) PJ2.binds PJ2.perm PJ2.hl rfl canon0 hsz PJ2K30.hk
  have n31 := cnt3_proved (bs := bs) PJ2.binds PJ2.perm PJ2.hl rfl canon1 hsz PJ2K31.hk
  refine ⟨⟨PJ2.chain, PJ2.orbits⟩, PJ2.ords, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [PairJ2.blocks, PairJ2.groups, PairJ2.levels, n2.1]
    exact Nat.eq_of_beq_eq_true s2
  · rw [PairJ2.blocks, PairJ2.groups, PairJ2.levels, n30.1]
    exact Nat.eq_of_beq_eq_true s3
  · intro c hc
    rw [cl_eq] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · rw [rep0_eq]
      exact ordWK_sound o0
    · rw [rep1_eq]
      exact ordWK_sound o1
  · intro c hc
    rw [cl_eq] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact cl0.1
    · exact cl1.1
  · rw [cl_eq]
    unfold keysDistinctNF
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [closureOf, closureOf, PairJ2.levels, cl0.2.2, cl1.2.2]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at srt
    exact srt
  · rw [cl_eq]
    refine sum_two ?_
    rw [closureOf, closureOf, PairJ2.levels, cl0.2.1, cl1.2.1]
    exact Nat.eq_of_beq_eq_true sSz
  · rw [cl_eq]
    refine wsum_two
      (f := fun w => countW (fun y => ordB bs y (nat_lit 3) && condsOK bs w y conds) blocks [])
      (n₀ := countW (fun y => ordB bs y (nat_lit 3) && condsOK bs wA y conds) blocks [])
      (n₁ := countW (fun y => ordB bs y (nat_lit 3) &&
        condsOK bs (List.replicate 6 (patW wA wB commPat)).flatten y conds) blocks []) rfl rfl ?_
    rw [closureOf, closureOf, PairJ2.levels, cl0.2.1, cl1.2.1, PairJ2.blocks, PairJ2.groups,
      rep1_eq, rep0_eq, PairJ2.levels, n30.2, n31.2]
    exact Nat.eq_of_beq_eq_true sTot

end CertificateChecks.KernelSporSch.PJ2Facts

end
