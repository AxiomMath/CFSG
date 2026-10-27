module

public import Certificates.Kernel.Misc.Perm.HS100.TSyChecks
public import Certificates.Kernel.Misc.Perm.HS100.TGlue
public import CFSG.Certificates.Kernel.PGrpMul

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.HS100.T

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.PGrp
  CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.EvenSporadicStandard.HSStd CFSG.EvenSporadicStandard.HSStd.Zassenhaus
open CFSG.KC.Misc.ArrEnum (permB memK any_eqA_unpack')
open CertificateChecks.KernelMisc.HS100
open CertificateChecks.KernelMisc.HS100.Five (eqA_F hidA pidPP and_of)
open CertificateChecks.KernelMisc.HS100.S0 (listOf Z0)

theorem tKeysLt : ∀ p ∈ zasTKeys, p < 100 := by decide

theorem tSize : zasTCert.pts.size = TT.N := by rw [tPin.2, Array.size_ofFn]

theorem tGet : ∀ i < TT.N, zasTCert.pts[i]! = unpack 100 7 (TT.T i) := fun i hi => by
  rw [tPin.2, getElem!_pos _ i (by rw [Array.size_ofFn]; exact hi), Array.getElem_ofFn]

theorem tPerm : ∀ i < TT.N, permB 100 7 (TT.T i) = true := fun i hi =>
  allN_spec tperm i (by rw [← nums'.2.1]; exact hi)

theorem zPerm : permB 100 7 Z0 = true := (and_of S0.zperm).1

theorem zMem : permOfArr 100 (unpack 100 7 Z0) ∈ Subgroup.closure (permsA 100 zasTGens) :=
  mem_of_memK sz tKeysLt tPin.1 tSize tGet (by rw [nums'.2.1]; exact syMem)

theorem commAll : (zasTCert.pts.toList.all fun x =>
    eqA 100 (compA 100 s5Z x) (compA 100 x s5Z)) = true := by
  rw [listOf tPin.2, List.all_map, List.all_eq_true]
  intro i hi
  have hi' := List.mem_range.1 hi
  have hi5 : i < 512 := by rw [← nums'.2.1]; exact hi'
  have hm := mem_of_pt sz tKeysLt tPin.1 tSize tGet hi'
  simp only [Function.comp_apply]
  rw [z_eq, eqA_keyCK sz tKeysLt tPin.1 zPerm (tPerm i hi') (tPerm i hi') zPerm zMem hm hm zMem]
  exact allN_spec syComm i hi5

theorem zAny : zasTCert.pts.toList.any (eqA 100 s5Z) = true := by
  rw [z_eq, any_eqA_unpack' sz tSize tGet tPerm zPerm, nums'.2.1]
  exact syMem

theorem zasSylowOK_true : zasSylowOK = true := by
  have hz1 : validA 100 s5Z = true := by rw [z_eq]; exact validA_unpack zPerm
  have hz2 : eqA 100 s5Z (idA 100) = false := by
    rw [z_eq, hidA, eqA_F cZ pidPP.1]; exact S0.prods'.2.1
  have hz3 : eqA 100 (compA 100 s5Z s5Z) (idA 100) = true := by
    rw [z_eq, compA_unpack cZ cZ, hidA, eqA_F (canonK_pcomp cZ cZ) pidPP.1]; exact S0.prods'.1
  have hz4 : s5InP s5Z = true := by rw [z_eq]; exact s5InP_unpack (and_of S0.ssift).2
  have hsz : (zasTCert.pts.size == 512) = true := by
    rw [tSize, nums'.2.1]; rfl
  have hg : allLt zasTGens.size (fun k => s5InP zasTGens[k]!) = true := by
    rw [allLt_iff]
    intro k hk
    have hk3 : k < 3 := by simpa [zasTGens, zasGens] using hk
    rw [t_get k hk3]
    exact s5InP_unpack (allN_spec sySift k hk3)
  unfold zasSylowOK
  rw [tPin.1, hsz, hg, hz1, hz4, hz2, hz3, commAll, zAny]
  rfl

end CertificateChecks.KernelMisc.HS100.T

end
