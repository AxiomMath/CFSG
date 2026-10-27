module

public import Certificates.Kernel.LocalComp.Co3SurjS
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Co3Surj

open CFSG.KC.SurjK CFSG.KC.M1F2 CFSG.KLie.CT
open CFSG.KS (lget)
open CFSG.Sporadic.Bridge.SurjD.Native CFSG.EvenSmallLie.SympSix.Co3Ident

theorem kIT : wordsK IT.chars IW.W = true := by quickRfl
theorem kST : wordsK ST.chars SW.W = true := by quickRfl
theorem kA : m1Bind SA.chars 22 CS.A = true := by quickRfl
theorem kB : m1Bind SB.chars 22 CS.B = true := by quickRfl
theorem kAI : Nat.beq (mulF 22 CS.A CS.AI) (idF 22) = true := by quickRfl
theorem kBI : Nat.beq (mulF 22 CS.B CS.BI) (idF 22) = true := by quickRfl

@[expose] noncomputable def Li : List (List Int) :=
  (IW.W.toArray.set! 3 (sDok.flatMap fun i => IW.W.toArray[i]!)).toList

@[expose] noncomputable def Ls : List (List Int) := SW.W.map fun w => w.flatMap substD

theorem kSizes : (Li.length == 7 && Ls.length == 2 && CS.Ims.length == 7 &&
    CS.ImsI.length == 7) = true := by decide +kernel

theorem kBase : Li.all (fun w => w.all fun z => decide (0 ≤ z) && decide (z < 4)) = true := by
  decide +kernel

theorem kSl : Ls.all (fun w => w.all fun z => z != 0 && decide (z.natAbs ≤ 7)) = true := by
  decide +kernel

theorem kImg0 : Nat.beq (matW 22 (baseF CS.A CS.AI CS.B CS.BI) (Li.getD 0 [])) (lget CS.Ims 0) = true := by quickRfl
theorem kImg1 : Nat.beq (matW 22 (baseF CS.A CS.AI CS.B CS.BI) (Li.getD 1 [])) (lget CS.Ims 1) = true := by quickRfl
theorem kImg2 : Nat.beq (matW 22 (baseF CS.A CS.AI CS.B CS.BI) (Li.getD 2 [])) (lget CS.Ims 2) = true := by quickRfl
theorem kImg4 : Nat.beq (matW 22 (baseF CS.A CS.AI CS.B CS.BI) (Li.getD 4 [])) (lget CS.Ims 4) = true := by quickRfl
theorem kImg5 : Nat.beq (matW 22 (baseF CS.A CS.AI CS.B CS.BI) (Li.getD 5 [])) (lget CS.Ims 5) = true := by quickRfl
theorem kImg6 : Nat.beq (matW 22 (baseF CS.A CS.AI CS.B CS.BI) (Li.getD 6 [])) (lget CS.Ims 6) = true := by quickRfl

theorem kInv : CFSG.KC.Enum.allN 7 (fun k => Nat.beq (mulF 22 (lget CS.Ims k) (lget CS.ImsI k)) (idF 22)) = true := by
  quickRfl

theorem kRel : vSpec.rels.all (fun r => r.all (fun l => decide (l.1 < 7)) &&
    Nat.beq (matW 22 (imgF CS.Ims CS.ImsI) (r.map letterOf)) (idF 22)) = true := by quickRfl

theorem kSA : Nat.beq (matW 22 (imgF CS.Ims CS.ImsI) (Ls.getD 0 [])) CS.A = true := by quickRfl
theorem kSB : Nat.beq (matW 22 (imgF CS.Ims CS.ImsI) (Ls.getD 1 [])) CS.B = true := by quickRfl

theorem Li3 : Li.getD 3 [] = sDok.flatMap WI := by decide +kernel

end CertificateChecks.KernelLC.Co3Surj

end
