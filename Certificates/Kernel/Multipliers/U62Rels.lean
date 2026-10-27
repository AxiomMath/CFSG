module

public import Certificates.Kernel.Multipliers.U62Base

set_option exponentiation.threshold 2048
set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelU62

open CFSG.Certificates.LabZ CertificateChecks.KernelMult

@[expose] def ρ0 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem r0 : zprod gg 21 (fun d => ρ0.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U52C.sY0 (by decide)

@[expose] def ρ1 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem r1 : zprod gg 21 (fun d => ρ1.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U52C.sY1 (by decide)

@[expose] def ρ2 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem r2 : zprod gg 21 (fun d => ρ2.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U52C.sY2 (by decide)

@[expose] def ρ3 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem r3 : zprod gg 21 (fun d => ρ3.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U52C.sY3 (by decide)

@[expose] def ρ4 : List ℤ :=
  [0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem r4 : zprod gg 21 (fun d => ρ4.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U52C.sY4 (by decide)

@[expose] def ρ5 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem r5 : zprod gg 21 (fun d => ρ5.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U52C.sY5 (by decide)

@[expose] def ρ6 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0]

theorem r6 : zprod gg 21 (fun d => ρ6.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U52C.sY6 (by decide)

@[expose] def ρ7 : List ℤ :=
  [3, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0]

theorem r7 : zprod gg 21 (fun d => ρ7.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U52C.sY7 (by decide)

@[expose] def ρ8 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem r8 : zprod gg 21 (fun d => ρ8.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U52C.sY8 (by decide)

@[expose] def ρ9 : List ℤ :=
  [0, 9, 0, 0, 0, 15, 0, 45, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -45]

theorem r9 : zprod gg 21 (fun d => ρ9.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U52C.sY9 (by decide)

@[expose] def ρ10 : List ℤ :=
  [0, -6, 0, 0, 0, -10, 0, -27, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30]

theorem r10 : zprod gg 21 (fun d => ρ10.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U52C.sY10 (by decide)

@[expose] def ρ11 : List ℤ :=
  [0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem r11 : zprod gg 21 (fun d => ρ11.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U52C.sY11 (by decide)

@[expose] def ρ12 : List ℤ :=
  [0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem r12 : zprod gg 21 (fun d => ρ12.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U52C.sY12 (by decide)

@[expose] def ρ13 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem r13 : zprod gg 21 (fun d => ρ13.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U52C.sY13 (by decide)

@[expose] def ρ14 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0]

theorem r14 : zprod gg 21 (fun d => ρ14.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U52C.sY14 (by decide)

@[expose] def ρ15 : List ℤ :=
  [1, 8, 0, -1, 0, 9, 10, 21, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, -1, 0, -30]

theorem r15 : zprod gg 21 (fun d => ρ15.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U52C.sY15 (by decide)

@[expose] def ρ16 : List ℤ :=
  [0, -9, 0, 0, 0, -15, 0, -46, -2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 45]

theorem r16 : zprod gg 21 (fun d => ρ16.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U52C.sY16 (by decide)

@[expose] def ρ17 : List ℤ :=
  [-3, 0, 0, 0, -1, 0, 4, 0, 0, -2, -2, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0]

theorem r17 : zprod gg 21 (fun d => ρ17.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U52C.sY17 (by decide)

@[expose] def ρ18 : List ℤ :=
  [-2, -10, 0, -1, 0, -9, -9, -13, -1, -1, -1, 1, 0, 2, 0, 0, 0, 0, -1, 0, 30]

theorem r18 : zprod gg 21 (fun d => ρ18.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U52C.sY18 (by decide)

@[expose] def ρ19 : List ℤ :=
  [0, -9, 0, -1, -2, -15, -2, -49, 4, 0, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 45]

theorem r19 : zprod gg 21 (fun d => ρ19.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U52C.sY19 (by decide)

@[expose] def ρ20 : List ℤ :=
  [0, 0, 0, 0, 0, 0, -1, -9, 2, -1, 0, -1, 1, 0, -1, 0, 0, 0, 0, 0, 0]

theorem r20 : zprod gg 21 (fun d => ρ20.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U52C.sY20 (by decide)

@[expose] def ρ21 : List ℤ :=
  [-3, 0, 0, 0, 1, 0, -7, -11, 1, -3, -1, 0, 1, 0, -1, 2, 0, 0, 0, 0, 0]

theorem r21 : zprod gg 21 (fun d => ρ21.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U52C.sY21 (by decide)

@[expose] def ρ22 : List ℤ :=
  [0, 15, 0, 2, 6, 25, 16, 29, 3, -1, -4, 1, 0, 0, 1, 0, 0, 0, 0, 0, -75]

theorem r22 : zprod gg 21 (fun d => ρ22.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U52C.sY22 (by decide)

@[expose] def ρ23 : List ℤ :=
  [-9, 55, -4, 6, -13, 128, 96, 294, -32, -11, 10, 4, -6, 12, 8, 10, 0, -1, 0, 0, -360]

theorem r23 : zprod gg 21 (fun d => ρ23.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U52C.sY23 (by decide)

@[expose] def ρ24 : List ℤ :=
  [36, -3, -5, 8, -11, -56, -5, -22, -5, 18, -1, 5, -3, -9, -1, -3, 0, 0, 0, -1, 150]

theorem r24 : zprod gg 21 (fun d => ρ24.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U52C.sY24 (by decide)

@[expose] def ρ25 : List ℤ :=
  [61, -117, -5, -31, -15, -186, -152, -269, 39, -27, 16, 21, -3, 6, -7, -30, -1, 0, 0, 0, 570]

theorem r25 : zprod gg 21 (fun d => ρ25.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U52C.sY25 (by decide)

@[expose] def ρ26 : List ℤ :=
  [27, 27, 5, -15, 16, -12, -45, 97, 25, -6, 5, 15, -7, -18, 17, -21, 0, 0, 0, -1, 0]

theorem r26 : zprod gg 21 (fun d => ρ26.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U52C.sY26 (by decide)

@[expose] def rhos : List (List ℤ) :=
  [ρ0, ρ1, ρ2, ρ3, ρ4, ρ5, ρ6, ρ7, ρ8, ρ9, ρ10, ρ11, ρ12, ρ13, ρ14, ρ15, ρ16, ρ17, ρ18, ρ19,
    ρ20, ρ21, ρ22, ρ23, ρ24, ρ25, ρ26]

theorem rhos_one : ∀ ρ ∈ rhos, zprod gg 21 (fun d => ρ.getD d 0) = 1 := by
  intro ρ hρ
  simp only [rhos, List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl
  · exact r0
  · exact r1
  · exact r2
  · exact r3
  · exact r4
  · exact r5
  · exact r6
  · exact r7
  · exact r8
  · exact r9
  · exact r10
  · exact r11
  · exact r12
  · exact r13
  · exact r14
  · exact r15
  · exact r16
  · exact r17
  · exact r18
  · exact r19
  · exact r20
  · exact r21
  · exact r22
  · exact r23
  · exact r24
  · exact r25
  · exact r26

@[expose] def c0 : List ℤ :=
  [0, 6381805566320311, -3991684444799240, 242549932093026890, 6381805566320311,
    10373490345699116, -6381805900899876, 6384473503551090, 121274966046513445,
    4794667974371489, 4794667974371334, 111749565553, 0, 5334536143127, 6381805566320311, -1,
    1598446380308020, 3192459581747412, 1, -224837449293, -15955625723603401, 3192013921803639,
    -669159136, 0, 1, -2, -1]

@[expose] def τ0 : List ℤ :=
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]

theorem t0 : zprod gg 21 (fun d => τ0.getD d 0) = 1 :=
  zprod_target gg_comm 21 c0 rhos rhos_one _ (by decide)

@[expose] def c1 : List ℤ :=
  [0, -4478476921432586, 2801192621414295, -170211120016934568, -4478476921432586,
    -7279669777640426, 4478477156226131, -4480349165140648, -85105560008467284,
    -3364691958414417, -3364691958414375, -78421043209, 0, -3743548242019, -4478476921432586,
    -14, -1121720984753709, -2240330955069621, 14, 157781260690, 11196972522523244,
    -2240018210071020, 469587128, -5, 2, 0, -2]

@[expose] def τ1 : List ℤ :=
  [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0]

theorem t1 : zprod gg 21 (fun d => τ1.getD d 0) = 1 :=
  zprod_target gg_comm 21 c1 rhos rhos_one _ (by decide)

@[expose] def c2 : List ℤ :=
  [0, 20524837475041275, -12837851863354405, 780076717169882274, 20524837475041275,
    33362690414453437, -20524838551099032, 20533417958649434, 390038358584941137,
    15420366524498925, 15420366524498307, 359403251553, 0, 17156662984389, 20524837475041275,
    -30, 5140841698707884, 10267425633711877, 30, -723110733645, -51315669427135572,
    10265992324937395, -2152115474, -9, 8, -9, -8]

@[expose] def τ2 : List ℤ :=
  [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 0, 0, 0]

theorem t2 : zprod gg 21 (fun d => τ2.getD d 0) = 1 :=
  zprod_target gg_comm 21 c2 rhos rhos_one _ (by decide)

@[expose] def c3 : List ℤ :=
  [0, -7193951017902, 4499664252755, -273416717688998, -7193951017902, -11693615647815,
    7193951395060, -7196958475518, -136708358844499, -5404835073127, -5404835073127, -125970761,
    0, -6013406600, -7193951017902, 0, -1801863884002, -3598730424964, 0, 253450153,
    17986130840674, -3598228050554, 754316, 0, 0, 0, 0]

@[expose] def τ3 : List ℤ :=
  [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem t3 : zprod gg 21 (fun d => τ3.getD d 0) = 1 :=
  zprod_target gg_comm 21 c3 rhos rhos_one _ (by decide)

@[expose] def c4 : List ℤ :=
  [0, 896482924, -560731108, 34072155516, 896482924, 1457214079, -896482971, 896857697,
    17036077758, 673530053, 673530053, 15698, 0, 749358, 896482924, 0, 224541445, 448460150, 0,
    -31584, -2241363489, 448397547, -94, 0, 0, 0, 0]

@[expose] def τ4 : List ℤ :=
  [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem t4 : zprod gg 21 (fun d => τ4.getD d 0) = 1 :=
  zprod_target gg_comm 21 c4 rhos rhos_one _ (by decide)

@[expose] def c5 : List ℤ :=
  [0, -312586420709, 195516196837, -11880307904950, -312586420709, -508102633934, 312586437097,
    -312717098620, -5940153952475, -234847032752, -234847032753, -5473590, 0, -261290271,
    -312586420709, -2, -78293302359, -156369463717, -1, 11012735, 781520509097, -156347634903,
    32776, 0, 0, 0, 0]

@[expose] def τ5 : List ℤ :=
  [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0]

theorem t5 : zprod gg 21 (fun d => τ5.getD d 0) = 1 :=
  zprod_target gg_comm 21 c5 rhos rhos_one _ (by decide)

@[expose] def c6 : List ℤ :=
  [0, 171666943, -107374042, 6524455316, 171666943, 279040994, -171666952, 171738708,
    3262227658, 128973840, 128973840, 3006, 0, 143494, 171666943, 0, 42997298, 85875348, 0,
    -6048, -429197264, 85863360, -18, 0, 0, 0, 0]

@[expose] def τ6 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem t6 : zprod gg 21 (fun d => τ6.getD d 0) = 1 :=
  zprod_target gg_comm 21 c6 rhos rhos_one _ (by decide)

@[expose] def c7 : List ℤ :=
  [0, 0, 0, -2, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def τ7 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem t7 : zprod gg 21 (fun d => τ7.getD d 0) = 1 :=
  zprod_target gg_comm 21 c7 rhos rhos_one _ (by decide)

@[expose] def c8 : List ℤ :=
  [0, 2448181654073515, -1531285860255897, 93046754210237538, 2448181654073515,
    3979467642680483, -2448181782424586, 2449205125396047, 46523377105118769, 1839325571775441,
    1839325571775384, 42869252802, 0, 2046429240755, 2448181654073515, 9, 613194347998176,
    1224688044501476, -9, -86251909869, -6120880645743741, 1224517080894559, -256702136, 0, -1,
    0, -1]

@[expose] def τ8 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0]

theorem t8 : zprod gg 21 (fun d => τ8.getD d 0) = 1 :=
  zprod_target gg_comm 21 c8 rhos rhos_one _ (by decide)

@[expose] def c9 : List ℤ :=
  [0, 2448181577777097, -1531285812534101, 93046751310479662, 2448181577777097,
    3979467518662265, -2448181706128164, 2449205049067733, 46523375655239831, 1839325514453735,
    1839325514453678, 42869251466, 0, 2046429176980, 2448181577777097, 9, 613194328888266,
    1224688006334655, -9, -86251907181, -6120880454989404, 1224517042733066, -256702128, 0, -1,
    0, -1]

@[expose] def τ9 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0]

theorem t9 : zprod gg 21 (fun d => τ9.getD d 0) = 1 :=
  zprod_target gg_comm 21 c9 rhos rhos_one _ (by decide)

@[expose] def c10 : List ℤ :=
  [0, 2448181577777097, -1531285812534101, 93046751310479662, 2448181577777097,
    3979467518662265, -2448181706128164, 2449205049067733, 46523375655239831, 1839325514453735,
    1839325514453678, 42869251466, 0, 2046429176979, 2448181577777097, 9, 613194328888266,
    1224688006334655, -9, -86251907181, -6120880454989404, 1224517042733066, -256702128, 0, -1,
    0, -1]

@[expose] def τ10 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0]

theorem t10 : zprod gg 21 (fun d => τ10.getD d 0) = 1 :=
  zprod_target gg_comm 21 c10 rhos rhos_one _ (by decide)

@[expose] def c11 : List ℤ :=
  [0, 2448181558702995, -1531285800603653, 93046750585540286, 2448181558702995,
    3979467487657714, -2448181687054061, 2449205029985657, 46523375292770143, 1839325500123310,
    1839325500123253, 42869251132, 0, 2046429161035, 2448181558702995, 9, 613194324110789,
    1224687996792951, -9, -86251906509, -6120880407300826, 1224517033192694, -256702126, 0, -1,
    0, -1]

@[expose] def τ11 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0]

theorem t11 : zprod gg 21 (fun d => τ11.getD d 0) = 1 :=
  zprod_target gg_comm 21 c11 rhos rhos_one _ (by decide)

@[expose] def c12 : List ℤ :=
  [0, 2448181568240048, -1531285806568878, 93046750948010050, 2448181568240048,
    3979467503159993, -2448181696591115, 2449205039526697, 46523375474005025, 1839325507288524,
    1839325507288467, 42869251299, 0, 2046429169007, 2448181568240048, 9, 613194326499528,
    1224688001563804, -9, -86251906845, -6120880431145120, 1224517037962881, -256702127, 0, -1,
    0, -1]

@[expose] def τ12 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0]

theorem t12 : zprod gg 21 (fun d => τ12.getD d 0) = 1 :=
  zprod_target gg_comm 21 c12 rhos rhos_one _ (by decide)

@[expose] def c13 : List ℤ :=
  [0, -155742579135795, 97413690228067, -5919226400876606, -155742579135795, -253156277528956,
    155742587300889, -155807687892863, -2959613200438303, -117009825617825, -117009825617952,
    -2727153778, 0, -130184854105, -155742579135795, -19, -39008734957051, -77909281923854, 21,
    5486968206, 389383580570728, -77898405969046, 16330264, -10, 4, -2, -6]

@[expose] def τ13 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 10, -2, 2, 0]

theorem t13 : zprod gg 21 (fun d => τ13.getD d 0) = 1 :=
  zprod_target gg_comm 21 c13 rhos rhos_one _ (by decide)

@[expose] def c14 : List ℤ :=
  [0, 2448181568240043, -1531285806568876, 93046750948009880, 2448181568240043,
    3979467503159986, -2448181696591110, 2449205039526693, 46523375474004940, 1839325507288521,
    1839325507288464, 42869251299, 0, 2046429169008, 2448181568240043, 9, 613194326499527,
    1224688001563802, -9, -86251906845, -6120880431145109, 1224517037962879, -256702127, 0, -1,
    0, -1]

@[expose] def τ14 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0]

theorem t14 : zprod gg 21 (fun d => τ14.getD d 0) = 1 :=
  zprod_target gg_comm 21 c14 rhos rhos_one _ (by decide)

@[expose] def c15 : List ℤ :=
  [0, 13185237760459845, -8247087430423658, 501124405968692232, 13185237760459845,
    21432325882147301, -13185238451723643, 13190749897480159, 250562202984346116,
    9906105187251025, 9906105187250709, 230882087524, 0, 11021508985143, 13185237760459845, 12,
    3302497287434715, 6595835330387354, -12, -464529230102, -32965391470540045,
    6594914567092729, -1382527596, 0, 0, -3, -3]

@[expose] def τ15 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 3, 0]

theorem t15 : zprod gg 21 (fun d => τ15.getD d 0) = 1 :=
  zprod_target gg_comm 21 c15 rhos rhos_one _ (by decide)

@[expose] def taus : List (List ℤ) :=
  [τ0, τ1, τ2, τ3, τ4, τ5, τ6, τ7, τ8, τ9, τ10, τ11, τ12, τ13, τ14, τ15]

theorem tau_shape : ∀ k < 16, ∀ d < 21, (taus.getD k []).getD d 0 = (if d = k then 1 else 0) ∨
    (16 ≤ d ∧ d < 20) := by
  decide

theorem tau_eq : ∀ k < 16, zprod gg 21 (fun d => (taus.getD k []).getD d 0) = 1 := by
  intro k hk
  interval_cases k
  exacts [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15]

theorem z₁_eq_one {k : ℕ} (hk : k < 16) : z₁ k = 1 := by
  rw [← gg_rel hk, ← tau_eq k hk]
  refine (zprod_eq_single (by omega) ?_ fun d hd hdk => ?_).symm
  · rcases tau_shape k hk k (by omega) with h | h
    · simp only [h, ↓reduceIte]
    · omega
  · rcases tau_shape k hk d hd with h | h
    · simp only [h, hdk, ↓reduceIte, zpow_zero]
    · rw [show d = 16 + (d - 16) by omega, gg_cover (by omega), one_zpow]

end CertificateChecks.KernelU62

end
