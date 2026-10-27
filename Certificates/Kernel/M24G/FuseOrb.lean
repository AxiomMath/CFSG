module

public import CFSG.Certificates.Kernel.M24G.FuseFastSound
public import Certificates.Kernel.M24G.FuseChecksFA
public import Certificates.Kernel.M24G.FuseChecksFB

public section

namespace CFSG.KC.M24G.FuseC

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G

theorem piA_V : DuadV Native.fusePiATab := duadV_of _ (by decide)

theorem piB_V : DuadV Native.fusePiBTab := duadV_of _ (by decide)

theorem piA_key : Native.kzeroKey Native.fusePiATab = fusePiAP := by decide +kernel

theorem piB_key : Native.kzeroKey Native.fusePiBTab = fusePiBP := by decide +kernel

theorem replayA : replayOK (fun c => c) fuseStepsP (Native.kzeroKey Native.fusePiATab) 32000
    FuseD.aL FuseD.aPar FuseD.aGen (balTree FuseS.aS) = true := by
  rw [piA_key, ← fuseStepsF_eq]
  exact fuseOrbA_okF

theorem replayB : replayOK (fun c => c) fuseStepsP (Native.kzeroKey Native.fusePiBTab) 32000
    FuseD.bL FuseD.bPar FuseD.bGen (balTree FuseS.bS) = true := by
  rw [piB_key, ← fuseStepsF_eq]
  exact fuseOrbB_okF

theorem mem_fuseOrbA {t : Array Nat} (ht : DuadV t) :
    t ∈ (Native.fuseOrbit Native.fusePiATab).1.toList ↔ Native.kzeroKey t ∈ FuseD.aL :=
  mem_fuseOrbit piA_V replayA ht

theorem mem_fuseOrbB {t : Array Nat} (ht : DuadV t) :
    t ∈ (Native.fuseOrbit Native.fusePiBTab).1.toList ↔ Native.kzeroKey t ∈ FuseD.bL :=
  mem_fuseOrbit piB_V replayB ht

theorem fuseTreeA : Native.treeValid Native.kzeroValid (Native.fuseConjSteps (Native.fusePairs ()))
    Native.fusePiATab (Native.fuseOrbit Native.fusePiATab) = true :=
  fuseOrbit_treeValid piA_V

theorem fuseTreeB : Native.treeValid Native.kzeroValid (Native.fuseConjSteps (Native.fusePairs ()))
    Native.fusePiBTab (Native.fuseOrbit Native.fusePiBTab) = true :=
  fuseOrbit_treeValid piB_V

end CFSG.KC.M24G.FuseC
