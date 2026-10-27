
module

public import Certificates.Kernel.SporSch.Co2M.WordsBase
public import CFSG.Sporadic.Co2Schreier.ChainsBase
public import CFSG.Sporadic.Co2Schreier.OrbitZCheck
public import CFSG.Sporadic.Co2Schreier.OrbitTCheck
public import CFSG.Certificates.NativeSetOrbit
public import CFSG.Sporadic.Schreier.Co3Centralizers
public import CFSG.Certificates.Kernel.Spor.RawOrbSound
public import CFSG.LocalAnalysis.ComponentInitial.AutomorphismRealization
public import CFSG.Sporadic.Co2Schreier.OrbitCheck
public meta import CFSG.Sporadic.Co2Schreier.OrbitCheck
public import CFSG.Certificates.Kernel.Spor.ONKSound

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2M CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Mathieu CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

theorem permK_eq {c : ChainRecord} {PS : ℕ → ℕ} {kS nb BP k : ℕ} {a : Array ℕ} {p : ℕ × ℕ}
    {g : Equiv.Perm (Fin 2300)} (hb : Binds 2300 12 PS kS nb BP c.strongArrs c.baseArr)
    (hk : k < kS) (ha : MatRep.Rep 22 co2PackedVecs a p.1 p.2)
    (h : bindK (PV 0) (PS k) p.1 p.2 = true) (hg : Rep 2300 a g) :
    permOfArr 2300 c.strongArrs[k]! = g := by
  obtain ⟨-, -, -, -, hS, -⟩ := hb
  rw [hS k hk, unpack_eq ha h]
  exact (rep_permOfArr (isInvA_rep ha)).1.unique hg

theorem getD_memK {l : List (Equiv.Perm (Fin 2300))} {k : ℕ} (hk : k < l.length) :
    l.getD k 1 ∈ l := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

theorem card_mul_leK
    {H : Subgroup (Equiv.Perm (Fin 2300))} {x : Equiv.Perm (Fin 2300)} (hx : x ∈ co2P)
    (hH : H ≤ co2P ⊓ Subgroup.centralizer {x}) {N : ℕ}
    (horb : N ≤ (Set.range fun g : co2P => g • {p : Fin 2300 | x p = p}).ncard) :
    Nat.card H * N ≤ 42305421312000 := by
  set xP : co2P := ⟨x, hx⟩
  set Δ : Set (Fin 2300) := {p | xP • p = p}
  have hK : H.subgroupOf co2P ≤ MulAction.stabilizer co2P Δ := by
    intro g hg
    have hg' := Subgroup.mem_subgroupOf.1 hg
    have hc : g ∈ Subgroup.centralizer {xP} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hH hg').2)
    exact MulAction.mem_stabilizer_iff.2 (smul_fixedSet_of_mem_centralizer hc)
  have hHle : H ≤ co2P := fun g hg => (hH hg).1
  have hcard : Nat.card H = Nat.card (H.subgroupOf co2P) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHle).toEquiv).symm
  have hidx : (MulAction.stabilizer co2P Δ).index = (Set.range fun g : co2P => g • Δ).ncard :=
    MulAction.index_stabilizer _ _
  have hm := (MulAction.stabilizer co2P Δ).card_mul_index
  rw [card_co2P, hidx] at hm
  rw [hcard, ← hm]
  exact Nat.mul_le_mul (Subgroup.card_le_of_le hK) horb

theorem recordOK_of_cardK {n w kS kO nb BP NS CH : ℕ} {PS PSI LR : ℕ → ℕ} {c : ChainRecord}
    (hg : c.generators = c.strongGenerators.take kO) (hgl : c.generators.length = kO)
    (hd : c.derivations.length + kO = kS) (hb : Binds n w PS kS nb BP c.strongArrs c.baseArr)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO c.derivations nb BP = true)
    (ho : OrbsOK n w PS PSI LR kS nb BP NS CH) (hN : n ≤ NS * CH)
    (hcard : Nat.card (Subgroup.closure (Set.range fun j : Fin kO =>
      permOfArr n c.strongArrs[j.val]!)) ≤ (recordOrbits n c).prod) :
    recordOK n c 4 = true := by
  unfold recordOK
  rw [origArrs_eq hg, wordArrs_eq hgl hd]
  exact rawChainK_of_card_orb 4 hb hh ho hN hcard

end CertificateChecks.KernelSporSch.Co2M

end
