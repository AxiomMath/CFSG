module

public import Certificates.Data.Kernel.OpsMcertN
public import Certificates.Data.Kernel.OpsFpK
public import Certificates.Kernel.SporSch.Ly.BSData
public import Certificates.Kernel.SporSch.Ly.SevA
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.LyThreeInputs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.LyFiveInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelMC

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.KC.Ord CFSG.KD.OrdLy CFSG.SectionRank.Native
open CFSG.RankThree.Asc83Table.Native CFSG.AGLEmbedding.R3
open CertificateChecks.KernelSporSch

noncomputable abbrev OL : Ops Nat Nat := opsFpK 5 12 1332 111 8 L H CM RM ONE

@[expose] noncomputable def notStabL (X : Nat) : Bool :=
  !Nat.beq (mulR 5 12 1332 111 8 L H CM RM X LySv.UP)
    (mulR 5 12 1332 111 8 L H CM RM LySv.UP
      (Nat.land (mulR 5 12 1332 111 8 L H CM RM X LySv.UP) (2 ^ (7 * 1332) - 1)))

theorem ly3_K : regsN OL LyBS.A LyBS.B lyThreeN lyThreeProg (fun R =>
    certN OL R ⟨lyThreeN, lyThreeProg, lyTzSpec.facts ++ lyCzSpec.facts⟩ &&
      OL.eq (getN R 0) LyBS.A && OL.eq (getN R 1) LyBS.B &&
      decide (lyTzSpec.gen.rc0 < lyThreeN) && decide (lyTzSpec.gen.rc1 < lyThreeN) &&
      OL.eq (getN R lyTzSpec.gen.rc0) (LyBS.CF 0) &&
      OL.eq (getN R lyTzSpec.gen.rc1) (LyBS.CF 1)) = true := by
  quickRfl

theorem ly5_K : regsN OL LyBS.A LyBS.B lyFiveN lyFiveProg (fun R =>
    certN OL R ⟨lyFiveN, lyFiveProg, lyTzSpec5.facts ++ lyCzSpec5.facts⟩ &&
      OL.eq (getN R 0) LyBS.A && OL.eq (getN R 1) LyBS.B &&
      (List.range 5).all (fun j => decide ((lyTzSpec5.gen.els.getD j default).reg < lyFiveN) &&
        OL.eq (getN R (lyTzSpec5.gen.els.getD j default).reg) (LySv.AF (j + 2))) &&
      decide (lyTzSpec5.gen.rs < lyFiveN) && notStabL (getN R lyTzSpec5.gen.rs)) = true := by
  quickRfl

theorem ly3_neg : (!regsN OL LyBS.A LyBS.B lyThreeN lyThreeProg (fun R =>
    OL.eq (getN R lyTzSpec.gen.rc0) (LyBS.CF 1))) = true := by
  quickRfl

theorem ly5_neg : (!notStabL (LySv.AF 2)) = true := by
  quickRfl

end CertificateChecks.KernelMC

end
