module

public import Certificates.Kernel.Heis.Q8
public import Certificates.Data.Kernel.U38N
public import Certificates.Data.HuppertU38F.Data

public section

set_option maxRecDepth 1000000

#kc_arg_chars CertificateChecks.KernelHeis.WS HuppertU38F.wordsS
#kc_arg_chars CertificateChecks.KernelHeis.WC HuppertU38F.wordsCw

namespace CertificateChecks.KernelHeis

open CFSG.LieType.SeitzGeneration.HeisSmall CFSG.KC.HeisWords CFSG.KC.HeisN HuppertU38F

@[expose] noncomputable def letters188005 : List (M3 Nat) :=
  words1_8.map (fk8.evalN (rawGens8.map matN))

@[expose] noncomputable def rows188005 : List (List Nat × List (M3 Nat) × List (List Nat)) := [
  ([0, 0, 1, 1, 0, 0, 0, 1, 0], rawGensS.map matN, decodeL WS.chars),
  ([0, 0, 1, 1, 0, 0, 0, 8, 0], rawGensCw.map matN, decodeL WC.chars),
  ([0, 1, 0, 0, 0, 9, 1, 0, 0], rawGensCw.map matN, decodeL WC.chars),
  ([1, 0, 0, 0, 1, 0, 0, 0, 8], letters188005, [[0], [1], [2], [3]]),
  ([1, 0, 0, 0, 1, 0, 0, 0, 9], letters188005, [[0], [1], [2], [3]])]

theorem u38_gu : (fk8.guListN 8).all (fun g => fk8.unitaryOkN g && fk8.entriesL4N 8 g) = true := by
  decide +kernel

theorem u38_cover : fk8.coverN 8 ((decodeL W8.chars).map (fk8.evalN letters188005)) = true := by
  decide +kernel

theorem u38_table :
    rows188005.all (fun r => fk8.u38EntryOkN 8 letters188005 (matN r.1) r.2.1 r.2.2) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem u38_class : fk8.forallUnitaryN 8 (fk8.classOkN 8
    (fk8.bitsF4 8 (rows188005.flatMap fun r => fk8.orbitN (fk8.guListN 8) (matN r.1)))) = true := by
  decide +kernel

theorem u38_k : fk8.u38N 8 rawGens8 words1_8 (decodeL W8.chars) rows188005 = true :=
  FK.u38N_of_parts fk8 u38_gu u38_cover u38_table u38_class

theorem u38_neg_cover :
    fk8.coverN 8 ((decodeL W8.chars).dropLast.map (fk8.evalN letters188005)) = false := by
  decide +kernel

theorem u38_neg_gen :
    (rows188005.map fun r => (r.1, matN [1, 0, 0, 0, 8, 0, 0, 0, 8] :: r.2.1.tail, r.2.2)).all
      (fun r => fk8.u38EntryOkN 8 letters188005 (matN r.1) r.2.1 r.2.2) = false := by
  decide +kernel

theorem u38_neg_letters :
    (rows188005.map fun r => (r.1, r.2.1, r.2.2.reverse)).all
      (fun r => fk8.u38EntryOkN 8 letters188005 (matN r.1) r.2.1 r.2.2) = false := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem u38_neg_class : fk8.forallUnitaryN 8 (fk8.classOkN 8
    (fk8.bitsF4 8 (rows188005.dropLast.flatMap fun r => fk8.orbitN (fk8.guListN 8) (matN r.1)))) =
      false := by
  decide +kernel

end CertificateChecks.KernelHeis
