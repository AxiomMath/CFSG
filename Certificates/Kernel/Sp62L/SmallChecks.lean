module

public import Certificates.Data.Kernel.Sp62L.Step
public import Certificates.Kernel.Sp62L.Data

public section

namespace CertificateChecks.KernelSp62L

open CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.Quasithin.G2U CFSG.KGroups.Sp6 CFSG.KC.Sp62L

theorem ch9440rt_ : replayB gensT 81 SD.ET SD.PT SD.CT SD.POST = true := by decide +kernel

theorem ch9440rb_ : replayB gensB 27 SD.EB SD.PB SD.CB SD.POSB = true := by decide +kernel

theorem ch9440re_ : replayB gensE 27 SD.EE SD.PE SD.CE SD.POSE = true := by decide +kernel

theorem ch9440rd_ : replayB gensD 9 SD.ED SD.PD SD.CD SD.POSD = true := by decide +kernel

theorem ch9440t_ : (gensT.all genB && SD.ET.toArray.size == 81 && allCheck validB SD.ET.toArray &&
    (fun _ => true) SD.ET.toArray) = true := by
  decide +kernel

theorem ch9440b_ : (gensB.all genB && SD.EB.toArray.size == 27 && allCheck validB SD.EB.toArray &&
    (gensB.all (inTab SD.ET.toArray) &&
      (propB2 SD.EB.toArray && (propB3 SD.EB.toArray && propB4 SD.EB.toArray)))) = true := by
  decide +kernel

theorem ch9440e_ : (gensE.all genB && SD.EE.toArray.size == 27 && allCheck validB SD.EE.toArray &&
    (gensE.all (inTab SD.ET.toArray) && (propE2 SD.EE.toArray && (propE3 SD.EE.toArray &&
      (propE4 SD.EE.toArray && (propE5 SD.EE.toArray && (propE6 SD.EE.toArray &&
      (propE7 SD.EE.toArray && (propE8 SD.EE.toArray && (propE9 SD.EE.toArray &&
      (propE10 SD.EE.toArray && (propE11 SD.EE.toArray && (propE12 SD.EE.toArray &&
      (propE13 SD.EE.toArray && propE14 SD.EE.toArray)))))))))))))) = true := by
  decide +kernel

theorem ch9440d_ : (gensD.all genB && SD.ED.toArray.size == 9 && allCheck validB SD.ED.toArray &&
    (gensD.all (inTab SD.EE.toArray) && (propD2 SD.ED.toArray && (propD3 SD.ED.toArray &&
      (propD4 SD.ED.toArray && propD5 SD.ED.toArray))))) = true := by
  decide +kernel

theorem ch5169_ : allCheck (fun x => !(commB x cSg) || inZ x) SD.EB.toArray = true := by
  decide +kernel

theorem ch9440nb_ :
    replayB gensB 27 (SD.EB.getD 1 [] :: SD.EB.getD 0 [] :: SD.EB.drop 2) SD.PB SD.CB SD.POSB =
      false := by
  decide +kernel

theorem ch9440nt_ : replayB gensB 81 SD.ET SD.PT SD.CT SD.POST = false := by decide +kernel

theorem ch9440ne_ : allCheck (fun x => !(gensE.all (commB x)) || x == oneC) SD.EE.toArray = false := by
  decide +kernel

theorem ch5169n_ : allCheck (fun x => !(commB x cTau) || inZ x) SD.EB.toArray = false := by
  decide +kernel

end CertificateChecks.KernelSp62L

end
