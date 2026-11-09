module

public import Certificates.Kernel.SporSch.PairBT.McLClsZ
public import Certificates.Kernel.SporSch.PairBT.McLCent
public import Certificates.Kernel.SporSch.PairBT.McLSylChk
public import Certificates.Data.Kernel.SporSch.ZOrbK
public import CFSG.Certificates.Kernel.SporSch.ClsZSound
public import CFSG.Certificates.Kernel.SporSch.CntZKProof
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.McLZOrb

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.MBT CFSG.KS.SporSch.MOC

@[expose] noncomputable def chk : Nat → Bool :=
  zOrbK 275 9 (mask 9) 2025 11 CertificateChecks.KernelSporSch.McLSylChk.Z McLZC.RP McLZC.OT
    McLZC.clsD

theorem hr : zRepLtK 2025 McLZC.clsD.c McLZC.RP = true := by
  quickRfl

end CertificateChecks.KernelSporSch.McLZOrb

#kss_slices CertificateChecks.KernelSporSch.McLZOrbS CertificateChecks.KernelSporSch.McLZOrb.chk 256 88

namespace CertificateChecks.KernelSporSch.McLZOrb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.MBT CFSG.Sporadic.Schreier CFSG.Monster.B.Mathieu
open CertificateChecks.KernelSporSch

theorem sem {gA gB : Equiv.Perm (Fin 275)}
    (hA : imageList gA = (unpack 275 9 (PMcL.S 0)).toList)
    (hB : imageList gB = (unpack 275 9 (PMcL.S 1)).toList) :
    ClsSem 275 9 (gen2 gA gB) gA 2 McLZC.clsD := by
  have hn : 275 < 2 ^ 32 := by norm_num
  have pA := prep_of_imageList hA
  have pB := prep_of_imageList hB
  have pAi := prep_of_imageList (invK_rep hA (allN_spec PMcLCheck.perm 0 (by decide)))
  have pBi := prep_of_imageList (invK_rep hB (allN_spec PMcLCheck.perm 1 (by decide)))
  obtain ⟨z, hz⟩ := exists_perm_of_permOK McLSylChk.pZ
  have pZ := prep_of_imageList hz
  have pZi := prep_of_imageList (invK_rep hz McLSylChk.pZ)
  have hzK : z ∈ Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin 275))) :=
    chainS_mem_proved McLCent.mclChainS hA hB McLCent.mcl_base_nodup hz McLSylChk.cZ McLSylChk.sZ
  have hO : ∀ k < McLZC.clsD.c,
      zOrbK 275 9 (mask 9) 2025 11 McLSylChk.Z McLZC.RP McLZC.OT McLZC.clsD k = true :=
    elems_of_slices (nb := 88) (by decide) McLZOrbS.all
  have hT : ∀ j < 2025, zRepTreeK 275 9 (mask 9) (PMcL.S 0) (PMcL.SI 0) (PMcL.S 1) (PMcL.SI 1)
      McLSylChk.Z McLSylChk.Zi McLZC.RP McLZC.OT McLZC.clsD j = true := by
    intro j hj
    have h := elems_of_slices (c := 2025) (nb := 8) (by norm_num) McLZCT.all j hj
    unfold McLZC.tree at h
    have hb : Nat.blt j 2025 = true := by
      rw [Nat.blt_eq]
      exact hj
    rw [hb] at h
    exact h
  have hs : ∀ k < McLZC.clsD.c, clsSrtK (275 * 9) McLZC.clsD k = true :=
    elems_of_slices (nb := 88) (by decide) McLZCS.all
  refine ⟨entryZ_mem_class hn pA pAi pB pBi hzK pZ pZi McLZC.hd hO pA hT, fun x hx => ?_,
    fun k hk => clsSrtK_facts hk (hs k hk), ordIs_sound McLSylChk.sz hA McLSylChk.cA McLSylChk.oA⟩
  exact (memZ_class_iff hn pA pAi pB pBi hzK pZ pZi McLZC.hd hO pA (by norm_num) hs hT
    (McLCent.ncard_le hA hB) x).1 hx

end CertificateChecks.KernelSporSch.McLZOrb

end
