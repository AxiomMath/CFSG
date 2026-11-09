module

public import Certificates.Kernel.Sporadic.Fi22.WordKit
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveCoreData
public import CFSG.Certificates.Kernel.Spor.PK.Perm.WordAppend
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatVal

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22WV

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.AGLEmbedding.KFactProofs.Fi22Five CFSG.AGLEmbedding.KFactProofs.Fi22Guest
open CertificateChecks.KernelSpor

#kc_natval X2 := wordK 3510 12 (mask 12) (pidn 3510 12) Fi22W.G Fi22W.GI (((signedWord wx).drop 82).drop 82)
#kc_natval X1 := wordK 3510 12 (mask 12) X2 Fi22W.G Fi22W.GI (((signedWord wx).drop 82).take 82)
#kc_natval Xv := wordK 3510 12 (mask 12) X1 Fi22W.G Fi22W.GI ((signedWord wx).take 82)

theorem X2_eq : wordK 3510 12 (mask 12) (pidn 3510 12) Fi22W.G Fi22W.GI (((signedWord wx).drop 82).drop 82) = X2 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem X1_eq : wordK 3510 12 (mask 12) X2 Fi22W.G Fi22W.GI (((signedWord wx).drop 82).take 82) = X1 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem X_v : Fi22W.W (signedWord wx) = Xv := by
  rw [Fi22W.W, ← List.take_append_drop 82 (signedWord wx), wordK_append,
    ← List.take_append_drop 82 ((signedWord wx).drop 82), wordK_append, X2_eq, X1_eq]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

#kc_natval Y2 := wordK 3510 12 (mask 12) (pidn 3510 12) Fi22W.G Fi22W.GI (((signedWord wy).drop 70).drop 70)
#kc_natval Y1 := wordK 3510 12 (mask 12) Y2 Fi22W.G Fi22W.GI (((signedWord wy).drop 70).take 70)
#kc_natval Yv := wordK 3510 12 (mask 12) Y1 Fi22W.G Fi22W.GI ((signedWord wy).take 70)

theorem Y2_eq : wordK 3510 12 (mask 12) (pidn 3510 12) Fi22W.G Fi22W.GI (((signedWord wy).drop 70).drop 70) = Y2 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem Y1_eq : wordK 3510 12 (mask 12) Y2 Fi22W.G Fi22W.GI (((signedWord wy).drop 70).take 70) = Y1 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem Y_v : Fi22W.W (signedWord wy) = Yv := by
  rw [Fi22W.W, ← List.take_append_drop 70 (signedWord wy), wordK_append,
    ← List.take_append_drop 70 ((signedWord wy).drop 70), wordK_append, Y2_eq, Y1_eq]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

#kc_natval N12 := wordK 3510 12 (mask 12) (pidn 3510 12) Fi22W.G Fi22W.GI (((nw1).drop 90).drop 90)
#kc_natval N11 := wordK 3510 12 (mask 12) N12 Fi22W.G Fi22W.GI (((nw1).drop 90).take 90)
#kc_natval N1v := wordK 3510 12 (mask 12) N11 Fi22W.G Fi22W.GI ((nw1).take 90)

theorem N12_eq : wordK 3510 12 (mask 12) (pidn 3510 12) Fi22W.G Fi22W.GI (((nw1).drop 90).drop 90) = N12 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem N11_eq : wordK 3510 12 (mask 12) N12 Fi22W.G Fi22W.GI (((nw1).drop 90).take 90) = N11 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem N1_v : Fi22W.W (nw1) = N1v := by
  rw [Fi22W.W, ← List.take_append_drop 90 (nw1), wordK_append,
    ← List.take_append_drop 90 ((nw1).drop 90), wordK_append, N12_eq, N11_eq]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

#kc_natval N22 := wordK 3510 12 (mask 12) (pidn 3510 12) Fi22W.G Fi22W.GI (((nw2).drop 76).drop 76)
#kc_natval N21 := wordK 3510 12 (mask 12) N22 Fi22W.G Fi22W.GI (((nw2).drop 76).take 76)
#kc_natval N2v := wordK 3510 12 (mask 12) N21 Fi22W.G Fi22W.GI ((nw2).take 76)

theorem N22_eq : wordK 3510 12 (mask 12) (pidn 3510 12) Fi22W.G Fi22W.GI (((nw2).drop 76).drop 76) = N22 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem N21_eq : wordK 3510 12 (mask 12) N22 Fi22W.G Fi22W.GI (((nw2).drop 76).take 76) = N21 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem N2_v : Fi22W.W (nw2) = N2v := by
  rw [Fi22W.W, ← List.take_append_drop 76 (nw2), wordK_append,
    ← List.take_append_drop 76 ((nw2).drop 76), wordK_append, N22_eq, N21_eq]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

#kc_natval Hv := wordK 3510 12 (mask 12) (pidn 3510 12) Fi22W.G Fi22W.GI (hw)

theorem H_v : Fi22W.W (hw) = Hv := by
  rw [Fi22W.W]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

#kc_natval Z2 := wordK 3510 12 (mask 12) (pidn 3510 12) Fi22W.G Fi22W.GI (((zw).drop 71).drop 71)
#kc_natval Z1 := wordK 3510 12 (mask 12) Z2 Fi22W.G Fi22W.GI (((zw).drop 71).take 71)
#kc_natval Zv := wordK 3510 12 (mask 12) Z1 Fi22W.G Fi22W.GI ((zw).take 71)

theorem Z2_eq : wordK 3510 12 (mask 12) (pidn 3510 12) Fi22W.G Fi22W.GI (((zw).drop 71).drop 71) = Z2 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem Z1_eq : wordK 3510 12 (mask 12) Z2 Fi22W.G Fi22W.GI (((zw).drop 71).take 71) = Z1 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem Z_v : Fi22W.W (zw) = Zv := by
  rw [Fi22W.W, ← List.take_append_drop 71 (zw), wordK_append,
    ← List.take_append_drop 71 ((zw).drop 71), wordK_append, Z2_eq, Z1_eq]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

#kc_natval U2 := wordK 3510 12 (mask 12) (pidn 3510 12) Fi22W.G Fi22W.GI (((uw).drop 73).drop 73)
#kc_natval U1 := wordK 3510 12 (mask 12) U2 Fi22W.G Fi22W.GI (((uw).drop 73).take 73)
#kc_natval Uv := wordK 3510 12 (mask 12) U1 Fi22W.G Fi22W.GI ((uw).take 73)

theorem U2_eq : wordK 3510 12 (mask 12) (pidn 3510 12) Fi22W.G Fi22W.GI (((uw).drop 73).drop 73) = U2 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem U1_eq : wordK 3510 12 (mask 12) U2 Fi22W.G Fi22W.GI (((uw).drop 73).take 73) = U1 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem U_v : Fi22W.W (uw) = Uv := by
  rw [Fi22W.W, ← List.take_append_drop 73 (uw), wordK_append,
    ← List.take_append_drop 73 ((uw).drop 73), wordK_append, U2_eq, U1_eq]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

end CertificateChecks.KernelSpor.Fi22WV

end
