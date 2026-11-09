module

public import Certificates.Data.Kernel.LocalQT.LatM
public import Certificates.Data.Kernel.LocalQT.ChainInj
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7LatticeInputs
public import CFSG.Certificates.Kernel.LocalQTListLemmas
public import CFSG.Certificates.Kernel.LocalQTPermSound
public import CFSG.Certificates.Kernel.LocalQTLat7RecSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4058

open CFSG.KC.LQT.L CFSG.KC.LQT.P CFSG.QuasithinUnique.Vol2Native.A312L.Seven
open CFSG.KC.LQT.S hiding code

@[expose] def C : List Lvl :=
  [(0, [6614517792, 5574330369, 6614516738, 5574296579, 6613435396, 4499506181, 5506139142], [0, 1, 2, 3, 4, 5, 6], 7),
    (1, [0, 6614517792, 5574329408, 6614484064, 5573248128, 6579881120, 4465951936], [0, 0, 1, 2, 3, 4, 5], 6),
    (2, [0, 0, 6614517792, 5574298656, 6613438496, 4499510304, 5506144288], [0, 0, 0, 1, 2, 3, 4], 5),
    (3, [0, 0, 0, 6614517792, 5573314592, 6579980320, 4466083872], [0, 0, 0, 0, 1, 2, 3], 4),
    (4, [0, 0, 0, 0, 6614517792, 4501637152, 5509318688], [0, 0, 0, 0, 0, 1, 2], 3)]

@[expose] noncomputable def k1cF (i : Nat) : Bool := closed7 C depth ((latGens.getD i []).map code)

#kc_each_unfold k1cF 0 12 as CFSG.KD.LQT.C4058.k1c
theorem k1 : allA latGens (fun G => closed7 C depth (G.map code)) = true :=
  allA_of_getD latGens _ [] (fun i hi => match i, hi with
    | 0, _ => k1c0
    | 1, _ => k1c1
    | 2, _ => k1c2
    | 3, _ => k1c3
    | 4, _ => k1c4
    | 5, _ => k1c5
    | 6, _ => k1c6
    | 7, _ => k1c7
    | 8, _ => k1c8
    | 9, _ => k1c9
    | 10, _ => k1c10
    | 11, _ => k1c11
    | k + 12, h => absurd h (by
      have : latGens.length = 12 := rfl
      omega))
theorem k2 : sizes7 C depth (latGens.map (List.map code)) [8, 24, 24, 24, 24, 24, 72, 120, 168, 168, 360, 2520] = true := by
  quickRfl
theorem k3 : cover7 C depth (dGens.map code) (reps.map code) = true := by quickRfl

theorem hok : chainOK 7 C = true := by quickRfl
theorem inj : chainInj 7 C = true := by quickRfl
theorem lenL : latGens.length = 12 := rfl
theorem eraseIdx_app_sub {α : Type} (L X : List α) (k : ℕ) : L.eraseIdx k ++ X ⊆ L ++ X := by
  intro x h
  rcases List.mem_append.1 h with h | h
  · exact List.mem_append_left _ (List.eraseIdx_subset h)
  · exact List.mem_append_right _ h
@[expose] def T0 : SetM := SetM.mk 3933741842641052864140959402544517475657761880617729080969908594763719777595230940140932321595054852238383227617543722531467868414467130693832553014042780236278070983787558070325507325511881696044924666531648800319911235487073827492749869029540413395167021776881212462975765178576304618477357671466177628168404400095090227371990775564408352764852703450499370404187297760738286576644706545252639413832722753025586018830214328953180623866902062300418501633706375137986673325210046560321285679316334389092037459728229021581313 8 [] true
theorem t0 : setEqM (bfsM 7 C (chainF C) ((latGens.getD 0 []).map code) depth) T0 = true := by
  quickRfl
theorem z0 : (latGens.getD 0 []).map code ∈ latGens.map (List.map code) :=
  getD_mem_map latGens code (by rw [lenL]; decide)
@[expose] def T1 : SetM := SetM.mk 34919996547111504648494988011944435376853628115784818725938998884644089385100209075275515315823497289434377214016215345157164516432370449364045759938088820655694322566573217235942383017966687272918184345539892428109961151919053028178862968440388375443149849240135155735859877037943199134417038201518618531505787685070302353083447382627993327727158699191940736419934022343878388332246719543353484228746371987798660422218520341644315589023873571239462589530435500792552818119085405041498682339536522694858496782852313403425289 24 [] true
theorem t1 : setEqM (bfsM 7 C (chainF C) ((latGens.getD 1 []).map code) depth) T1 = true := by
  quickRfl
theorem z1 : (latGens.getD 1 []).map code ∈ latGens.map (List.map code) :=
  getD_mem_map latGens code (by rw [lenL]; decide)
@[expose] def T2 : SetM := SetM.mk 11710446870016057372481163759882525100611952675377393494887343278258150414841187491034929295825278675509648531446072466305215885203067535219332292434111968857227795928659884409353625653639217048995275738059600659413889601026904394151493840880247230645612645511877759402819876801069286125867175453194734404162839743987138176755829600211024023071874400451102368988326248267426074346273141766307182742308995942559920137729645691731316437513626569573388249713338069603605227134058553242055060385340601978453553425877771867062275 24 [] true
theorem t2 : setEqM (bfsM 7 C (chainF C) ((latGens.getD 2 []).map code) depth) T2 = true := by
  quickRfl
theorem z2 : (latGens.getD 2 []).map code ∈ latGens.map (List.map code) :=
  getD_mem_map latGens code (by rw [lenL]; decide)
@[expose] def T3 : SetM := SetM.mk 19669891226988798232398402863782952480211137000667236722408634285927336408177229598007261307032389171479452161977232020770454814576489190461174241391497987135023810585499707166876255704744548260842093858948488811396692319484374383431530303947706888324938507751442570997384534819885350703265897929406222975506599302523305992019641572901227790518075893608047256438687431486565977217724666768019512705902527015438320381844504795351334211485177047620778232313145211360830946294058723286645290942396156749746634755151544996414725 24 [] true
theorem t3 : setEqM (bfsM 7 C (chainF C) ((latGens.getD 3 []).map code) depth) T3 = true := by
  quickRfl
theorem z3 : (latGens.getD 3 []).map code ∈ latGens.map (List.map code) :=
  getD_mem_map latGens code (by rw [lenL]; decide)
@[expose] def T4 : SetM := SetM.mk 4056671275224479322020217179621638131766850567998753554894403458925886453600161086955285044131500075683930476213637883554321410823605536841026384418080329150520125138395434575038579563106782469506550345158323417897531779209360544592132299243255977281352332765038217226942298143656353990213692359802267530723008375787211770006502102164327222243876873694894379929392518481943193571500937894946041062561566443981434334507804589640652007788347452530407017063394850279084984175196320627590533003949722856666975575419353292701825 24 [] true
theorem t4 : setEqM (bfsM 7 C (chainF C) ((latGens.getD 4 []).map code) depth) T4 = true := by
  quickRfl
theorem z4 : (latGens.getD 4 []).map code ∈ latGens.map (List.map code) :=
  getD_mem_map latGens code (by rw [lenL]; decide)
@[expose] def T5 : SetM := SetM.mk 83450903326495101000766580458366996114340253047941316384391272802500181048910968935457059435202039388213782936895036279159131207286538428724504538984143529998893212885146925064850519933686755810189712506522169347300420388323253726341845446393696001794757275701682053405246004668133556393560886884525282385400390727073406557288354464723720856156251935211267180233204273256692346433452109615835334204922719592799653940833261429006266772232926626339397186460332079824523250522940079689580432070929966397413969687028264237673154227661342345738582444683302230310047293379995197002557309403838989371902254421979651809832163527185162462256491298482677996828871443800557040930127658717653871053075284208913768489018801872368904119831477627191297 24 [] true
theorem t5 : setEqM (bfsM 7 C (chainF C) ((latGens.getD 5 []).map code) depth) T5 = true := by
  quickRfl
theorem z5 : (latGens.getD 5 []).map code ∈ latGens.map (List.map code) :=
  getD_mem_map latGens code (by rw [lenL]; decide)
@[expose] def T6 : SetM := SetM.mk 58555780391417680982971893607597998662470282717975015255219654123464303328933094430850193998027500655392258700800526548192753021792131319804081019139650765089631841267765569176234321962921589964127330288111358915858341145178470867875769805422977231509552269937850065974079291266825276098331730929523310557393021907082687609749448331211347305266427756594486630563778327297598773737811346336868302498021293130701577219809832431508076374210318454062780583719194506622113955746768862516825709633274001112449548160116296494860175 72 [] true
theorem t6 : setEqM (bfsM 7 C (chainF C) ((latGens.getD 6 []).map code) depth) T6 = true := by
  quickRfl
theorem z6 : (latGens.getD 6 []).map code ∈ latGens.map (List.map code) :=
  getD_mem_map latGens code (by rw [lenL]; decide)
@[expose] def T7 : SetM := SetM.mk 19669891226988798232398402863782952480211137000667236722408634309558926482733476015559191386112767075397712072734772936609001449848934126012664312969447308383467251441841719185950432414233009857361082631261868676505929820036673794292109093882920261752372346808114883972325966497901733105697826764070386390015188610642100213460984088466443889807747584421681277774906801760502374903746452666464451789900351046893074555583926565859940830574399444886035937146008552070913024070201838576962973715708816750101583039342608163882245 120 [] true
theorem t7 : setEqM (bfsM 7 C (chainF C) ((latGens.getD 7 []).map code) depth) T7 = true := by
  quickRfl
theorem z7 : (latGens.getD 7 []).map code ∈ latGens.map (List.map code) :=
  getD_mem_map latGens code (by rw [lenL]; decide)
@[expose] def T8 : SetM := SetM.mk 2745275198750711835076595461884998628592856509212044326375669887878569232844191784672418573854960376373286044736707008165174319960534596582742996044873750936275251047897215148499473007703966874836719581614566147580658056192635064852189907127950099040110499353763337083132128284439258325810758269619681659099292510580029489937228111335951059162843109943969625586884724556686107088334728795753157389355945848164770607258506489545966718868852258476091815765961888245137527083642641470451062040602687270815034204304476786530057332256643209194418059748105593378701756158463008081713895889775881452819676199340858592920794664712036776329722388779596615361637373268451704171964231411195405630401033352626923125945371994045290090193584374482401951747 168 [] true
theorem t8 : setEqM (bfsM 7 C (chainF C) ((latGens.getD 8 []).map code) depth) T8 = true := by
  quickRfl
theorem z8 : (latGens.getD 8 []).map code ∈ latGens.map (List.map code) :=
  getD_mem_map latGens code (by rw [lenL]; decide)
@[expose] def T9 : SetM := SetM.mk 705074645475758221977897614789067237586590844229364349609276787537222581409291366516969093990594343120473467123152321624178398600897654814937384864348796603335419417736079647374868357744890664120172815970429028561941819006654149011463253928380817744307765104578039813173810252645373700860733105054288170191862025646130870264139078030259088943881274205530494496541406303291344272999202246617357205737446690855662626655024438319848914065897131495044060210618990584113543899584344821854053979111044480538875857321260122274873268672351553115944956981728969554988972725063293267551538293130774769078604469437087410738223131180855981889007576565989782203135429139562082596028101836871478778386159907531207197469938351123950777267919590667600363649 168 [] true
theorem t9 : setEqM (bfsM 7 C (chainF C) ((latGens.getD 9 []).map code) depth) T9 = true := by
  quickRfl
theorem z9 : (latGens.getD 9 []).map code ∈ latGens.map (List.map code) :=
  getD_mem_map latGens code (by rw [lenL]; decide)
@[expose] def T10 : SetM := SetM.mk 116651009485079134256262034402945793114890130380292044975509655785937038451388013745858035818764995813810802993955306525645984670232827684524352414186468750680855355763816036345494374663145394664379354384703397458838527903734320604440898687770615442093738882275829062625829923682678484679522599306845835638132965686820234719765955359845886894823122319876082367676447617950872568534259573125113616114352600964619796579522359014277052173007799706174761843376381681188320002190334899243258720515023194890925116680032987475569780890407211901330272671276328603114643113872190253736507502234006067696570637152950295586978588131763409275257068477838898594653811687186149521155605003833795539190458902600758381380670522024843082411939479601982971663637 360 [] true
theorem t10 : setEqM (bfsM 7 C (chainF C) ((latGens.getD 10 []).map code) depth) T10 = true := by
  quickRfl
theorem z10 : (latGens.getD 10 []).map code ∈ latGens.map (List.map code) :=
  getD_mem_map latGens code (by rw [lenL]; decide)
@[expose] def T11 : SetM := SetM.mk 394084245522141626953485431836389151728191722497516426553221541823493367658800961065564478638820000356056388337167035542074008945401913950236214360506399705231203021164366069389563701733455174652493802096528279659381259483508916176782516892616322154881870596505654577774329808187256502370468256875376316278135937985788160888518809137837873180086327183792757748702946460720720770436177477377229784500022657580657233628383930137914619684009220791267089768552182903618603146950084219242780072578071648001265726679873751772302343114358428552134991938056446803917216962620267368806273089867659639177213488960155211698149211030681779788578141054359274289556411400436598704927821275214881488970218576557325551889577507340928956338410400961096026352642413831783448575 2520 [] true
theorem t11 : setEqM (bfsM 7 C (chainF C) ((latGens.getD 11 []).map code) depth) T11 = true := by
  quickRfl
theorem z11 : (latGens.getD 11 []).map code ∈ latGens.map (List.map code) :=
  getD_mem_map latGens code (by rw [lenL]; decide)
@[expose] def jS0 : List P7 := [perm7 [[2, 4, 5, 3, 6]], perm7 [[0, 1, 2, 3], [4, 5]], perm7 [[0, 2], [4, 5]]]
theorem jS0t : setEqM (bfsM 7 C (chainF C) (jS0.map code) 10) T11 = true := by quickRfl
@[expose] def jS1 : List P7 := [perm7 [[0, 1], [2, 6], [3, 5, 4]], perm7 [[0, 2, 4, 3, 6]], perm7 [[0, 3, 2, 1], [4, 5]], perm7 [[0, 4, 5, 3, 6]], perm7 [[0, 5, 3, 6, 2]], perm7 [[0, 5, 4, 3, 1, 6, 2]], perm7 [[0, 6, 2, 1, 5, 4, 3]]]
theorem jS1t : setEqM (bfsM 7 C (chainF C) (jS1.map code) 5) T11 = true := by quickRfl
@[expose] def jS2 : List P7 := [perm7 [[2, 3, 6, 4, 5]], perm7 [[0, 1], [2, 3]], perm7 [[0, 1, 2, 3], [4, 5]], perm7 [[0, 2], [1, 3]]]
theorem jS2t : setEqM (bfsM 7 C (chainF C) (jS2.map code) 10) T11 = true := by quickRfl
@[expose] def jS3 : List P7 := [perm7 [[2, 3, 5, 4, 6]], perm7 [[0, 1], [2, 3]], perm7 [[0, 1, 2, 3], [4, 5]], perm7 [[0, 2], [1, 3]]]
theorem jS3t : setEqM (bfsM 7 C (chainF C) (jS3.map code) 10) T11 = true := by quickRfl
@[expose] def jS4 : List P7 := [perm7 [[2, 3, 4, 5, 6]], perm7 [[0, 1], [2, 3]], perm7 [[0, 1, 2, 3], [4, 5]], perm7 [[0, 2], [1, 3]]]
theorem jS4t : setEqM (bfsM 7 C (chainF C) (jS4.map code) 10) T11 = true := by quickRfl
@[expose] def jS5 : List P7 := [perm7 [[1, 3], [4, 5]], perm7 [[0, 1], [2, 6, 4, 3]], perm7 [[0, 1, 2, 3, 6, 5, 4]], perm7 [[0, 1, 2, 4, 5, 6, 3]], perm7 [[0, 1, 2, 6, 4, 5, 3]], perm7 [[0, 2], [3, 6, 5, 4]], perm7 [[0, 3, 2, 1], [4, 5]], perm7 [[0, 3, 6, 4], [1, 2]]]
theorem jS5t : setEqM (bfsM 7 C (chainF C) (jS5.map code) 5) T11 = true := by quickRfl
@[expose] def jS6 : List P7 := [perm7 [[2, 4], [3, 6]], perm7 [[0, 1], [2, 3, 5, 4]], perm7 [[0, 1], [2, 5, 4, 3]], perm7 [[0, 2, 4, 5], [1, 3]], perm7 [[0, 2], [1, 4, 5, 3]], perm7 [[0, 4, 5, 2], [3, 6]], perm7 [[0, 4, 5, 3], [1, 2]], perm7 [[0, 5, 4, 3], [1, 2]]]
theorem jS6t : setEqM (bfsM 7 C (chainF C) (jS6.map code) 5) T11 = true := by quickRfl
@[expose] def jS7 : List P7 := [perm7 [[1, 5, 6, 3, 4]], perm7 [[0, 1, 4, 2, 3, 6, 5]], perm7 [[0, 1, 5, 2, 3, 6, 4]], perm7 [[0, 2], [1, 3]], perm7 [[0, 2], [1, 4], [3, 6, 5]], perm7 [[0, 2], [1, 5], [3, 6, 4]], perm7 [[0, 3, 6, 5, 2, 1, 4]], perm7 [[0, 3, 6, 4, 2, 1, 5]]]
theorem jS7t : setEqM (bfsM 7 C (chainF C) (jS7.map code) 5) T11 = true := by quickRfl
@[expose] def jS8 : List P7 := [perm7 [[2, 6, 4, 3, 5]], perm7 [[0, 1], [2, 3]], perm7 [[0, 1, 2, 3], [4, 5]]]
theorem jS8t : setEqM (bfsM 7 C (chainF C) (jS8.map code) 10) T11 = true := by quickRfl
theorem k4c0r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 0 1]).map code) depth) T0)
    (allL ((dGens ++ [reps.getD 0 1]).map code) (memM 7 C (chainF C) T0)) = true :=
  recG_monoR (G := latGens.getD 0 []) (G' := dGens ++ [reps.getD 0 1]) (Z := latGens.getD 0 []) hok inj (fun _ h => List.mem_append_left _ h) t0 (by quickRfl) k1c0 t0
theorem k4c0 : isLat7 C depth ((dGens ++ [reps.getD 0 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c0r z0 k1c0 t0
theorem k4c1r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 1 1]).map code) depth) T1)
    (allL ((dGens ++ [reps.getD 1 1]).map code) (memM 7 C (chainF C) T1)) = true :=
  recG_monoR (G := latGens.getD 1 []) (G' := dGens ++ [reps.getD 1 1]) (Z := latGens.getD 1 []) hok inj (fun _ h => h) t1 (by quickRfl) k1c1 t1
theorem k4c1 : isLat7 C depth ((dGens ++ [reps.getD 1 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c1r z1 k1c1 t1
theorem k4c2r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 2 1]).map code) depth) T11)
    (allL ((dGens ++ [reps.getD 2 1]).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 11 []) (G' := dGens ++ [reps.getD 2 1]) (Z := latGens.getD 11 []) hok inj (fun _ h => h) t11 (by quickRfl) k1c11 t11
theorem k4c2 : isLat7 C depth ((dGens ++ [reps.getD 2 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c2r z11 k1c11 t11
theorem k4c3r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 3 1]).map code) depth) T10)
    (allL ((dGens ++ [reps.getD 3 1]).map code) (memM 7 C (chainF C) T10)) = true :=
  recG_monoR (G := latGens.getD 10 []) (G' := dGens ++ [reps.getD 3 1]) (Z := latGens.getD 10 []) hok inj (fun _ h => h) t10 (by quickRfl) k1c10 t10
theorem k4c3 : isLat7 C depth ((dGens ++ [reps.getD 3 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c3r z10 k1c10 t10
theorem k4c4r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 4 1]).map code) depth) T11)
    (allL ((dGens ++ [reps.getD 4 1]).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_ballR (S := jS5) (m := 5) (k := 4) hok inj (by decide) jS5t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k4c4 : isLat7 C depth ((dGens ++ [reps.getD 4 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c4r z11 k1c11 t11
theorem k4c5r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 5 1]).map code) depth) T11)
    (allL ((dGens ++ [reps.getD 5 1]).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_ballR (S := jS5) (m := 5) (k := 4) hok inj (by decide) jS5t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k4c5 : isLat7 C depth ((dGens ++ [reps.getD 5 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c5r z11 k1c11 t11
theorem k4c6r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 6 1]).map code) depth) T7)
    (allL ((dGens ++ [reps.getD 6 1]).map code) (memM 7 C (chainF C) T7)) = true :=
  recG_monoR (G := latGens.getD 7 []) (G' := dGens ++ [reps.getD 6 1]) (Z := latGens.getD 7 []) hok inj (fun _ h => h) t7 (by quickRfl) k1c7 t7
theorem k4c6 : isLat7 C depth ((dGens ++ [reps.getD 6 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c6r z7 k1c7 t7
theorem k4c7r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 7 1]).map code) depth) T2)
    (allL ((dGens ++ [reps.getD 7 1]).map code) (memM 7 C (chainF C) T2)) = true :=
  recG_monoR (G := latGens.getD 2 []) (G' := dGens ++ [reps.getD 7 1]) (Z := latGens.getD 2 []) hok inj (fun _ h => h) t2 (by quickRfl) k1c2 t2
theorem k4c7 : isLat7 C depth ((dGens ++ [reps.getD 7 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c7r z2 k1c2 t2
theorem k4c8r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 8 1]).map code) depth) T3)
    (allL ((dGens ++ [reps.getD 8 1]).map code) (memM 7 C (chainF C) T3)) = true :=
  recG_monoR (G := latGens.getD 3 []) (G' := dGens ++ [reps.getD 8 1]) (Z := latGens.getD 3 []) hok inj (fun _ h => h) t3 (by quickRfl) k1c3 t3
theorem k4c8 : isLat7 C depth ((dGens ++ [reps.getD 8 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c8r z3 k1c3 t3
theorem k4c9r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 9 1]).map code) depth) T4)
    (allL ((dGens ++ [reps.getD 9 1]).map code) (memM 7 C (chainF C) T4)) = true :=
  recG_monoR (G := latGens.getD 4 []) (G' := dGens ++ [reps.getD 9 1]) (Z := latGens.getD 4 []) hok inj (fun _ h => h) t4 (by quickRfl) k1c4 t4
theorem k4c9 : isLat7 C depth ((dGens ++ [reps.getD 9 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c9r z4 k1c4 t4
theorem k4c10a : setEqM (bfsM 7 C (chainF C) ((dGens.eraseIdx 1 ++ [reps.getD 10 1]).map code) depth) T10 = true := by quickRfl
theorem k4c10r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 10 1]).map code) depth) T10)
    (allL ((dGens ++ [reps.getD 10 1]).map code) (memM 7 C (chainF C) T10)) = true :=
  recG_monoR (G := dGens.eraseIdx 1 ++ [reps.getD 10 1]) (G' := dGens ++ [reps.getD 10 1]) (Z := latGens.getD 10 []) hok inj (eraseIdx_app_sub _ _ 1) k4c10a (by quickRfl) k1c10 t10
theorem k4c10 : isLat7 C depth ((dGens ++ [reps.getD 10 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c10r z10 k1c10 t10
theorem k4c11r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 11 1]).map code) depth) T11)
    (allL ((dGens ++ [reps.getD 11 1]).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_ballR (S := jS4) (m := 10) (k := 2) hok inj (by decide) jS4t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k4c11 : isLat7 C depth ((dGens ++ [reps.getD 11 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c11r z11 k1c11 t11
theorem k4c12r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 12 1]).map code) depth) T11)
    (allL ((dGens ++ [reps.getD 12 1]).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_ballR (S := jS0) (m := 10) (k := 2) hok inj (by decide) jS0t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k4c12 : isLat7 C depth ((dGens ++ [reps.getD 12 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c12r z11 k1c11 t11
theorem k4c13r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 13 1]).map code) depth) T11)
    (allL ((dGens ++ [reps.getD 13 1]).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_ballR (S := jS1) (m := 5) (k := 4) hok inj (by decide) jS1t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k4c13 : isLat7 C depth ((dGens ++ [reps.getD 13 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c13r z11 k1c11 t11
theorem k4c14a : setEqM (bfsM 7 C (chainF C) ((dGens.eraseIdx 1 ++ [reps.getD 14 1]).map code) depth) T10 = true := by quickRfl
theorem k4c14r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 14 1]).map code) depth) T10)
    (allL ((dGens ++ [reps.getD 14 1]).map code) (memM 7 C (chainF C) T10)) = true :=
  recG_monoR (G := dGens.eraseIdx 1 ++ [reps.getD 14 1]) (G' := dGens ++ [reps.getD 14 1]) (Z := latGens.getD 10 []) hok inj (eraseIdx_app_sub _ _ 1) k4c14a (by quickRfl) k1c10 t10
theorem k4c14 : isLat7 C depth ((dGens ++ [reps.getD 14 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c14r z10 k1c10 t10
theorem k4c15r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 15 1]).map code) depth) T11)
    (allL ((dGens ++ [reps.getD 15 1]).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_ballR (S := jS3) (m := 10) (k := 2) hok inj (by decide) jS3t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k4c15 : isLat7 C depth ((dGens ++ [reps.getD 15 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c15r z11 k1c11 t11
theorem k4c16r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 16 1]).map code) depth) T11)
    (allL ((dGens ++ [reps.getD 16 1]).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_ballR (S := jS8) (m := 10) (k := 2) hok inj (by decide) jS8t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k4c16 : isLat7 C depth ((dGens ++ [reps.getD 16 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c16r z11 k1c11 t11
theorem k4c17a : setEqM (bfsM 7 C (chainF C) ((dGens.eraseIdx 1 ++ [reps.getD 17 1]).map code) depth) T7 = true := by quickRfl
theorem k4c17r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 17 1]).map code) depth) T7)
    (allL ((dGens ++ [reps.getD 17 1]).map code) (memM 7 C (chainF C) T7)) = true :=
  recG_monoR (G := dGens.eraseIdx 1 ++ [reps.getD 17 1]) (G' := dGens ++ [reps.getD 17 1]) (Z := latGens.getD 7 []) hok inj (eraseIdx_app_sub _ _ 1) k4c17a (by quickRfl) k1c7 t7
theorem k4c17 : isLat7 C depth ((dGens ++ [reps.getD 17 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c17r z7 k1c7 t7
theorem k4c18r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 18 1]).map code) depth) T11)
    (allL ((dGens ++ [reps.getD 18 1]).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_ballR (S := jS2) (m := 10) (k := 2) hok inj (by decide) jS2t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k4c18 : isLat7 C depth ((dGens ++ [reps.getD 18 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c18r z11 k1c11 t11
theorem k4c19r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 19 1]).map code) depth) T10)
    (allL ((dGens ++ [reps.getD 19 1]).map code) (memM 7 C (chainF C) T10)) = true := by quickRfl
theorem k4c19 : isLat7 C depth ((dGens ++ [reps.getD 19 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c19r z10 k1c10 t10
theorem k4c20r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 20 1]).map code) depth) T11)
    (allL ((dGens ++ [reps.getD 20 1]).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_ballR (S := jS2) (m := 10) (k := 2) hok inj (by decide) jS2t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k4c20 : isLat7 C depth ((dGens ++ [reps.getD 20 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c20r z11 k1c11 t11
theorem k4c21a : setEqM (bfsM 7 C (chainF C) ((dGens.eraseIdx 1 ++ [reps.getD 21 1]).map code) depth) T11 = true := by quickRfl
theorem k4c21r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 21 1]).map code) depth) T11)
    (allL ((dGens ++ [reps.getD 21 1]).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := dGens.eraseIdx 1 ++ [reps.getD 21 1]) (G' := dGens ++ [reps.getD 21 1]) (Z := latGens.getD 11 []) hok inj (eraseIdx_app_sub _ _ 1) k4c21a (by quickRfl) k1c11 t11
theorem k4c21 : isLat7 C depth ((dGens ++ [reps.getD 21 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c21r z11 k1c11 t11
theorem k4c22r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 22 1]).map code) depth) T9)
    (allL ((dGens ++ [reps.getD 22 1]).map code) (memM 7 C (chainF C) T9)) = true :=
  recG_monoR (G := latGens.getD 9 []) (G' := dGens ++ [reps.getD 22 1]) (Z := latGens.getD 9 []) hok inj (fun _ h => h) t9 (by quickRfl) k1c9 t9
theorem k4c22 : isLat7 C depth ((dGens ++ [reps.getD 22 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c22r z9 k1c9 t9
theorem k4c23r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 23 1]).map code) depth) T11)
    (allL ((dGens ++ [reps.getD 23 1]).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_ballR (S := jS3) (m := 10) (k := 2) hok inj (by decide) jS3t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k4c23 : isLat7 C depth ((dGens ++ [reps.getD 23 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c23r z11 k1c11 t11
theorem k4c24r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 24 1]).map code) depth) T11)
    (allL ((dGens ++ [reps.getD 24 1]).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_ballR (S := jS0) (m := 10) (k := 2) hok inj (by decide) jS0t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k4c24 : isLat7 C depth ((dGens ++ [reps.getD 24 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c24r z11 k1c11 t11
theorem k4c25r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 25 1]).map code) depth) T11)
    (allL ((dGens ++ [reps.getD 25 1]).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_ballR (S := jS4) (m := 10) (k := 2) hok inj (by decide) jS4t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k4c25 : isLat7 C depth ((dGens ++ [reps.getD 25 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c25r z11 k1c11 t11
theorem k4c26r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 26 1]).map code) depth) T11)
    (allL ((dGens ++ [reps.getD 26 1]).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_ballR (S := jS1) (m := 5) (k := 4) hok inj (by decide) jS1t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k4c26 : isLat7 C depth ((dGens ++ [reps.getD 26 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c26r z11 k1c11 t11
theorem k4c27r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 27 1]).map code) depth) T8)
    (allL ((dGens ++ [reps.getD 27 1]).map code) (memM 7 C (chainF C) T8)) = true :=
  recG_monoR (G := latGens.getD 8 []) (G' := dGens ++ [reps.getD 27 1]) (Z := latGens.getD 8 []) hok inj (fun _ h => h) t8 (by quickRfl) k1c8 t8
theorem k4c27 : isLat7 C depth ((dGens ++ [reps.getD 27 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c27r z8 k1c8 t8
theorem k4c28a : setEqM (bfsM 7 C (chainF C) ((dGens.eraseIdx 1 ++ [reps.getD 28 1]).map code) depth) T9 = true := by quickRfl
theorem k4c28r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 28 1]).map code) depth) T9)
    (allL ((dGens ++ [reps.getD 28 1]).map code) (memM 7 C (chainF C) T9)) = true :=
  recG_monoR (G := dGens.eraseIdx 1 ++ [reps.getD 28 1]) (G' := dGens ++ [reps.getD 28 1]) (Z := latGens.getD 9 []) hok inj (eraseIdx_app_sub _ _ 1) k4c28a (by quickRfl) k1c9 t9
theorem k4c28 : isLat7 C depth ((dGens ++ [reps.getD 28 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c28r z9 k1c9 t9
theorem k4c29a : setEqM (bfsM 7 C (chainF C) ((dGens.eraseIdx 1 ++ [reps.getD 29 1]).map code) depth) T10 = true := by quickRfl
theorem k4c29r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 29 1]).map code) depth) T10)
    (allL ((dGens ++ [reps.getD 29 1]).map code) (memM 7 C (chainF C) T10)) = true :=
  recG_monoR (G := dGens.eraseIdx 1 ++ [reps.getD 29 1]) (G' := dGens ++ [reps.getD 29 1]) (Z := latGens.getD 10 []) hok inj (eraseIdx_app_sub _ _ 1) k4c29a (by quickRfl) k1c10 t10
theorem k4c29 : isLat7 C depth ((dGens ++ [reps.getD 29 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c29r z10 k1c10 t10
theorem k4c30a : setEqM (bfsM 7 C (chainF C) ((dGens.eraseIdx 1 ++ [reps.getD 30 1]).map code) depth) T8 = true := by quickRfl
theorem k4c30r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 30 1]).map code) depth) T8)
    (allL ((dGens ++ [reps.getD 30 1]).map code) (memM 7 C (chainF C) T8)) = true :=
  recG_monoR (G := dGens.eraseIdx 1 ++ [reps.getD 30 1]) (G' := dGens ++ [reps.getD 30 1]) (Z := latGens.getD 8 []) hok inj (eraseIdx_app_sub _ _ 1) k4c30a (by quickRfl) k1c8 t8
theorem k4c30 : isLat7 C depth ((dGens ++ [reps.getD 30 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c30r z8 k1c8 t8
theorem k4c31a : setEqM (bfsM 7 C (chainF C) ((dGens.eraseIdx 1 ++ [reps.getD 31 1]).map code) depth) T11 = true := by quickRfl
theorem k4c31r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 31 1]).map code) depth) T11)
    (allL ((dGens ++ [reps.getD 31 1]).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := dGens.eraseIdx 1 ++ [reps.getD 31 1]) (G' := dGens ++ [reps.getD 31 1]) (Z := latGens.getD 11 []) hok inj (eraseIdx_app_sub _ _ 1) k4c31a (by quickRfl) k1c11 t11
theorem k4c31 : isLat7 C depth ((dGens ++ [reps.getD 31 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c31r z11 k1c11 t11
theorem k4c32a : setEqM (bfsM 7 C (chainF C) ((dGens.eraseIdx 1 ++ [reps.getD 32 1]).map code) depth) T11 = true := by quickRfl
theorem k4c32r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 32 1]).map code) depth) T11)
    (allL ((dGens ++ [reps.getD 32 1]).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := dGens.eraseIdx 1 ++ [reps.getD 32 1]) (G' := dGens ++ [reps.getD 32 1]) (Z := latGens.getD 11 []) hok inj (eraseIdx_app_sub _ _ 1) k4c32a (by quickRfl) k1c11 t11
theorem k4c32 : isLat7 C depth ((dGens ++ [reps.getD 32 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c32r z11 k1c11 t11
theorem k4c33a : setEqM (bfsM 7 C (chainF C) ((dGens.eraseIdx 1 ++ [reps.getD 33 1]).map code) depth) T11 = true := by quickRfl
theorem k4c33r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 33 1]).map code) depth) T11)
    (allL ((dGens ++ [reps.getD 33 1]).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := dGens.eraseIdx 1 ++ [reps.getD 33 1]) (G' := dGens ++ [reps.getD 33 1]) (Z := latGens.getD 11 []) hok inj (eraseIdx_app_sub _ _ 1) k4c33a (by quickRfl) k1c11 t11
theorem k4c33 : isLat7 C depth ((dGens ++ [reps.getD 33 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c33r z11 k1c11 t11
theorem k4c34a : setEqM (bfsM 7 C (chainF C) ((dGens.eraseIdx 1 ++ [reps.getD 34 1]).map code) depth) T11 = true := by quickRfl
theorem k4c34r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 34 1]).map code) depth) T11)
    (allL ((dGens ++ [reps.getD 34 1]).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := dGens.eraseIdx 1 ++ [reps.getD 34 1]) (G' := dGens ++ [reps.getD 34 1]) (Z := latGens.getD 11 []) hok inj (eraseIdx_app_sub _ _ 1) k4c34a (by quickRfl) k1c11 t11
theorem k4c34 : isLat7 C depth ((dGens ++ [reps.getD 34 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c34r z11 k1c11 t11
theorem k4c35a : setEqM (bfsM 7 C (chainF C) ((dGens.eraseIdx 1 ++ [reps.getD 35 1]).map code) depth) T10 = true := by quickRfl
theorem k4c35r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 35 1]).map code) depth) T10)
    (allL ((dGens ++ [reps.getD 35 1]).map code) (memM 7 C (chainF C) T10)) = true :=
  recG_monoR (G := dGens.eraseIdx 1 ++ [reps.getD 35 1]) (G' := dGens ++ [reps.getD 35 1]) (Z := latGens.getD 10 []) hok inj (eraseIdx_app_sub _ _ 1) k4c35a (by quickRfl) k1c10 t10
theorem k4c35 : isLat7 C depth ((dGens ++ [reps.getD 35 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c35r z10 k1c10 t10
theorem k4c36a : setEqM (bfsM 7 C (chainF C) ((dGens.eraseIdx 1 ++ [reps.getD 36 1]).map code) depth) T9 = true := by quickRfl
theorem k4c36r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 36 1]).map code) depth) T9)
    (allL ((dGens ++ [reps.getD 36 1]).map code) (memM 7 C (chainF C) T9)) = true :=
  recG_monoR (G := dGens.eraseIdx 1 ++ [reps.getD 36 1]) (G' := dGens ++ [reps.getD 36 1]) (Z := latGens.getD 9 []) hok inj (eraseIdx_app_sub _ _ 1) k4c36a (by quickRfl) k1c9 t9
theorem k4c36 : isLat7 C depth ((dGens ++ [reps.getD 36 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c36r z9 k1c9 t9
theorem k4c37a : setEqM (bfsM 7 C (chainF C) ((dGens.eraseIdx 1 ++ [reps.getD 37 1]).map code) depth) T11 = true := by quickRfl
theorem k4c37r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 37 1]).map code) depth) T11)
    (allL ((dGens ++ [reps.getD 37 1]).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := dGens.eraseIdx 1 ++ [reps.getD 37 1]) (G' := dGens ++ [reps.getD 37 1]) (Z := latGens.getD 11 []) hok inj (eraseIdx_app_sub _ _ 1) k4c37a (by quickRfl) k1c11 t11
theorem k4c37 : isLat7 C depth ((dGens ++ [reps.getD 37 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c37r z11 k1c11 t11
theorem k4c38r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 38 1]).map code) depth) T5)
    (allL ((dGens ++ [reps.getD 38 1]).map code) (memM 7 C (chainF C) T5)) = true :=
  recG_monoR (G := latGens.getD 5 []) (G' := dGens ++ [reps.getD 38 1]) (Z := latGens.getD 5 []) hok inj (fun _ h => h) t5 (by quickRfl) k1c5 t5
theorem k4c38 : isLat7 C depth ((dGens ++ [reps.getD 38 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c38r z5 k1c5 t5
theorem k4c39a : setEqM (bfsM 7 C (chainF C) ((dGens.eraseIdx 1 ++ [reps.getD 39 1]).map code) depth) T11 = true := by quickRfl
theorem k4c39r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 39 1]).map code) depth) T11)
    (allL ((dGens ++ [reps.getD 39 1]).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := dGens.eraseIdx 1 ++ [reps.getD 39 1]) (G' := dGens ++ [reps.getD 39 1]) (Z := latGens.getD 11 []) hok inj (eraseIdx_app_sub _ _ 1) k4c39a (by quickRfl) k1c11 t11
theorem k4c39 : isLat7 C depth ((dGens ++ [reps.getD 39 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c39r z11 k1c11 t11
theorem k4c40r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 40 1]).map code) depth) T11)
    (allL ((dGens ++ [reps.getD 40 1]).map code) (memM 7 C (chainF C) T11)) = true := by quickRfl
theorem k4c40 : isLat7 C depth ((dGens ++ [reps.getD 40 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c40r z11 k1c11 t11
theorem k4c41r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 41 1]).map code) depth) T11)
    (allL ((dGens ++ [reps.getD 41 1]).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_ballR (S := jS7) (m := 5) (k := 4) hok inj (by decide) jS7t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k4c41 : isLat7 C depth ((dGens ++ [reps.getD 41 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c41r z11 k1c11 t11
theorem k4c42a : setEqM (bfsM 7 C (chainF C) ((dGens.eraseIdx 1 ++ [reps.getD 42 1]).map code) depth) T8 = true := by quickRfl
theorem k4c42r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 42 1]).map code) depth) T8)
    (allL ((dGens ++ [reps.getD 42 1]).map code) (memM 7 C (chainF C) T8)) = true :=
  recG_monoR (G := dGens.eraseIdx 1 ++ [reps.getD 42 1]) (G' := dGens ++ [reps.getD 42 1]) (Z := latGens.getD 8 []) hok inj (eraseIdx_app_sub _ _ 1) k4c42a (by quickRfl) k1c8 t8
theorem k4c42 : isLat7 C depth ((dGens ++ [reps.getD 42 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c42r z8 k1c8 t8
theorem k4c43a : setEqM (bfsM 7 C (chainF C) ((dGens.eraseIdx 1 ++ [reps.getD 43 1]).map code) depth) T11 = true := by quickRfl
theorem k4c43r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 43 1]).map code) depth) T11)
    (allL ((dGens ++ [reps.getD 43 1]).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := dGens.eraseIdx 1 ++ [reps.getD 43 1]) (G' := dGens ++ [reps.getD 43 1]) (Z := latGens.getD 11 []) hok inj (eraseIdx_app_sub _ _ 1) k4c43a (by quickRfl) k1c11 t11
theorem k4c43 : isLat7 C depth ((dGens ++ [reps.getD 43 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c43r z11 k1c11 t11
theorem k4c44a : setEqM (bfsM 7 C (chainF C) ((dGens.eraseIdx 1 ++ [reps.getD 44 1]).map code) depth) T11 = true := by quickRfl
theorem k4c44r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 44 1]).map code) depth) T11)
    (allL ((dGens ++ [reps.getD 44 1]).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := dGens.eraseIdx 1 ++ [reps.getD 44 1]) (G' := dGens ++ [reps.getD 44 1]) (Z := latGens.getD 11 []) hok inj (eraseIdx_app_sub _ _ 1) k4c44a (by quickRfl) k1c11 t11
theorem k4c44 : isLat7 C depth ((dGens ++ [reps.getD 44 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c44r z11 k1c11 t11
theorem k4c45a : setEqM (bfsM 7 C (chainF C) ((dGens.eraseIdx 1 ++ [reps.getD 45 1]).map code) depth) T11 = true := by quickRfl
theorem k4c45r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 45 1]).map code) depth) T11)
    (allL ((dGens ++ [reps.getD 45 1]).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := dGens.eraseIdx 1 ++ [reps.getD 45 1]) (G' := dGens ++ [reps.getD 45 1]) (Z := latGens.getD 11 []) hok inj (eraseIdx_app_sub _ _ 1) k4c45a (by quickRfl) k1c11 t11
theorem k4c45 : isLat7 C depth ((dGens ++ [reps.getD 45 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c45r z11 k1c11 t11
theorem k4c46a : setEqM (bfsM 7 C (chainF C) ((dGens.eraseIdx 1 ++ [reps.getD 46 1]).map code) depth) T11 = true := by quickRfl
theorem k4c46r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 46 1]).map code) depth) T11)
    (allL ((dGens ++ [reps.getD 46 1]).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := dGens.eraseIdx 1 ++ [reps.getD 46 1]) (G' := dGens ++ [reps.getD 46 1]) (Z := latGens.getD 11 []) hok inj (eraseIdx_app_sub _ _ 1) k4c46a (by quickRfl) k1c11 t11
theorem k4c46 : isLat7 C depth ((dGens ++ [reps.getD 46 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c46r z11 k1c11 t11
theorem k4c47a : setEqM (bfsM 7 C (chainF C) ((dGens.eraseIdx 1 ++ [reps.getD 47 1]).map code) depth) T11 = true := by quickRfl
theorem k4c47r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 47 1]).map code) depth) T11)
    (allL ((dGens ++ [reps.getD 47 1]).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := dGens.eraseIdx 1 ++ [reps.getD 47 1]) (G' := dGens ++ [reps.getD 47 1]) (Z := latGens.getD 11 []) hok inj (eraseIdx_app_sub _ _ 1) k4c47a (by quickRfl) k1c11 t11
theorem k4c47 : isLat7 C depth ((dGens ++ [reps.getD 47 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c47r z11 k1c11 t11
theorem k4c48a : setEqM (bfsM 7 C (chainF C) ((dGens.eraseIdx 1 ++ [reps.getD 48 1]).map code) depth) T11 = true := by quickRfl
theorem k4c48r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((dGens ++ [reps.getD 48 1]).map code) depth) T11)
    (allL ((dGens ++ [reps.getD 48 1]).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := dGens.eraseIdx 1 ++ [reps.getD 48 1]) (G' := dGens ++ [reps.getD 48 1]) (Z := latGens.getD 11 []) hok inj (eraseIdx_app_sub _ _ 1) k4c48a (by quickRfl) k1c11 t11
theorem k4c48 : isLat7 C depth ((dGens ++ [reps.getD 48 1]).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k4c48r z11 k1c11 t11
theorem k4 : allA reps (fun r => isLat7 C depth ((dGens ++ [r]).map code) (latGens.map (List.map code))) = true :=
  allA_of_getD reps _ 1 (fun i hi => match i, hi with
    | 0, _ => k4c0
    | 1, _ => k4c1
    | 2, _ => k4c2
    | 3, _ => k4c3
    | 4, _ => k4c4
    | 5, _ => k4c5
    | 6, _ => k4c6
    | 7, _ => k4c7
    | 8, _ => k4c8
    | 9, _ => k4c9
    | 10, _ => k4c10
    | 11, _ => k4c11
    | 12, _ => k4c12
    | 13, _ => k4c13
    | 14, _ => k4c14
    | 15, _ => k4c15
    | 16, _ => k4c16
    | 17, _ => k4c17
    | 18, _ => k4c18
    | 19, _ => k4c19
    | 20, _ => k4c20
    | 21, _ => k4c21
    | 22, _ => k4c22
    | 23, _ => k4c23
    | 24, _ => k4c24
    | 25, _ => k4c25
    | 26, _ => k4c26
    | 27, _ => k4c27
    | 28, _ => k4c28
    | 29, _ => k4c29
    | 30, _ => k4c30
    | 31, _ => k4c31
    | 32, _ => k4c32
    | 33, _ => k4c33
    | 34, _ => k4c34
    | 35, _ => k4c35
    | 36, _ => k4c36
    | 37, _ => k4c37
    | 38, _ => k4c38
    | 39, _ => k4c39
    | 40, _ => k4c40
    | 41, _ => k4c41
    | 42, _ => k4c42
    | 43, _ => k4c43
    | 44, _ => k4c44
    | 45, _ => k4c45
    | 46, _ => k4c46
    | 47, _ => k4c47
    | 48, _ => k4c48
    | k + 49, h => absurd h (by
      have : reps.length = 49 := rfl
      omega))
theorem k5c0_0r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 0 [] ++ latGens.getD 0 []).map code) depth) T0)
    (allL ((latGens.getD 0 [] ++ latGens.getD 0 []).map code) (memM 7 C (chainF C) T0)) = true :=
  recG_sub (G₁ := latGens.getD 0 []) (G₂ := latGens.getD 0 []) (List.Subset.refl _) t0 (by quickRfl)
theorem k5c0_0 : isLat7 C depth ((latGens.getD 0 [] ++ latGens.getD 0 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c0_0r z0 k1c0 t0
theorem k5c0_1r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 0 [] ++ latGens.getD 1 []).map code) depth) T1)
    (allL ((latGens.getD 0 [] ++ latGens.getD 1 []).map code) (memM 7 C (chainF C) T1)) = true :=
  recG_dup (G₁ := latGens.getD 0 []) (D := dGens) (N := [perm7 [[4, 5, 6]]]) (List.Subset.refl _) t1 (by quickRfl)
theorem k5c0_1 : isLat7 C depth ((latGens.getD 0 [] ++ latGens.getD 1 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c0_1r z1 k1c1 t1
theorem k5c0_2r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 0 [] ++ latGens.getD 2 []).map code) depth) T2)
    (allL ((latGens.getD 0 [] ++ latGens.getD 2 []).map code) (memM 7 C (chainF C) T2)) = true :=
  recG_dup (G₁ := latGens.getD 0 []) (D := dGens) (N := [perm7 [[2, 3], [5, 6]]]) (List.Subset.refl _) t2 (by quickRfl)
theorem k5c0_2 : isLat7 C depth ((latGens.getD 0 [] ++ latGens.getD 2 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c0_2r z2 k1c2 t2
theorem k5c0_3r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 0 [] ++ latGens.getD 3 []).map code) depth) T3)
    (allL ((latGens.getD 0 [] ++ latGens.getD 3 []).map code) (memM 7 C (chainF C) T3)) = true :=
  recG_dup (G₁ := latGens.getD 0 []) (D := dGens) (N := [perm7 [[2, 3], [4, 5]]]) (List.Subset.refl _) t3 (by quickRfl)
theorem k5c0_3 : isLat7 C depth ((latGens.getD 0 [] ++ latGens.getD 3 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c0_3r z3 k1c3 t3
theorem k5c0_4r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 0 [] ++ latGens.getD 4 []).map code) depth) T4)
    (allL ((latGens.getD 0 [] ++ latGens.getD 4 []).map code) (memM 7 C (chainF C) T4)) = true :=
  recG_dup (G₁ := latGens.getD 0 []) (D := dGens) (N := [perm7 [[2, 3], [4, 6]]]) (List.Subset.refl _) t4 (by quickRfl)
theorem k5c0_4 : isLat7 C depth ((latGens.getD 0 [] ++ latGens.getD 4 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c0_4r z4 k1c4 t4
theorem k5c0_5r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 0 [] ++ latGens.getD 5 []).map code) depth) T5)
    (allL ((latGens.getD 0 [] ++ latGens.getD 5 []).map code) (memM 7 C (chainF C) T5)) = true :=
  recG_dup (G₁ := latGens.getD 0 []) (D := dGens) (N := [perm7 [[1, 4], [3, 5]]]) (List.Subset.refl _) t5 (by quickRfl)
theorem k5c0_5 : isLat7 C depth ((latGens.getD 0 [] ++ latGens.getD 5 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c0_5r z5 k1c5 t5
theorem k5c0_6r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 0 [] ++ latGens.getD 6 []).map code) depth) T6)
    (allL ((latGens.getD 0 [] ++ latGens.getD 6 []).map code) (memM 7 C (chainF C) T6)) = true :=
  recG_dup (G₁ := latGens.getD 0 []) (D := dGens) (N := [perm7 [[2, 3], [4, 5]], perm7 [[2, 3], [5, 6]]]) (List.Subset.refl _) t6 (by quickRfl)
theorem k5c0_6 : isLat7 C depth ((latGens.getD 0 [] ++ latGens.getD 6 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c0_6r z6 k1c6 t6
theorem k5c0_7r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 0 [] ++ latGens.getD 7 []).map code) depth) T7)
    (allL ((latGens.getD 0 [] ++ latGens.getD 7 []).map code) (memM 7 C (chainF C) T7)) = true :=
  recG_dup (G₁ := latGens.getD 0 []) (D := dGens) (N := [perm7 [[3, 6], [4, 5]]]) (List.Subset.refl _) t7 (by quickRfl)
theorem k5c0_7 : isLat7 C depth ((latGens.getD 0 [] ++ latGens.getD 7 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c0_7r z7 k1c7 t7
theorem k5c0_8r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 0 [] ++ latGens.getD 8 []).map code) depth) T8)
    (allL ((latGens.getD 0 [] ++ latGens.getD 8 []).map code) (memM 7 C (chainF C) T8)) = true :=
  recG_dup (G₁ := latGens.getD 0 []) (D := dGens) (N := [perm7 [[2, 5], [3, 6]]]) (List.Subset.refl _) t8 (by quickRfl)
theorem k5c0_8 : isLat7 C depth ((latGens.getD 0 [] ++ latGens.getD 8 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c0_8r z8 k1c8 t8
theorem k5c0_9r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 0 [] ++ latGens.getD 9 []).map code) depth) T9)
    (allL ((latGens.getD 0 [] ++ latGens.getD 9 []).map code) (memM 7 C (chainF C) T9)) = true :=
  recG_dup (G₁ := latGens.getD 0 []) (D := dGens) (N := [perm7 [[2, 4], [3, 6]]]) (List.Subset.refl _) t9 (by quickRfl)
theorem k5c0_9 : isLat7 C depth ((latGens.getD 0 [] ++ latGens.getD 9 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c0_9r z9 k1c9 t9
theorem k5c0_10r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 0 [] ++ latGens.getD 10 []).map code) depth) T10)
    (allL ((latGens.getD 0 [] ++ latGens.getD 10 []).map code) (memM 7 C (chainF C) T10)) = true :=
  recG_dup (G₁ := latGens.getD 0 []) (D := dGens) (N := [perm7 [[3, 4, 5]]]) (List.Subset.refl _) t10 (by quickRfl)
theorem k5c0_10 : isLat7 C depth ((latGens.getD 0 [] ++ latGens.getD 10 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c0_10r z10 k1c10 t10
theorem k5c0_11r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 0 [] ++ latGens.getD 11 []).map code) depth) T11)
    (allL ((latGens.getD 0 [] ++ latGens.getD 11 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_dup (G₁ := latGens.getD 0 []) (D := dGens) (N := [perm7 [[3, 4], [5, 6]]]) (List.Subset.refl _) t11 (by quickRfl)
theorem k5c0_11 : isLat7 C depth ((latGens.getD 0 [] ++ latGens.getD 11 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c0_11r z11 k1c11 t11
theorem k5c0 : allA latGens (fun G₂ => isLat7 C depth
    ((latGens.getD 0 [] ++ G₂).map code) (latGens.map (List.map code))) = true :=
  allA_of_getD latGens _ [] (fun j hj => match j, hj with
    | 0, _ => k5c0_0
    | 1, _ => k5c0_1
    | 2, _ => k5c0_2
    | 3, _ => k5c0_3
    | 4, _ => k5c0_4
    | 5, _ => k5c0_5
    | 6, _ => k5c0_6
    | 7, _ => k5c0_7
    | 8, _ => k5c0_8
    | 9, _ => k5c0_9
    | 10, _ => k5c0_10
    | 11, _ => k5c0_11
    | k + 12, h => absurd h (by
      have : latGens.length = 12 := rfl
      omega))
theorem k5c1_0r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 1 [] ++ latGens.getD 0 []).map code) depth) T1)
    (allL ((latGens.getD 1 [] ++ latGens.getD 0 []).map code) (memM 7 C (chainF C) T1)) = true :=
  recG_sub (G₁ := latGens.getD 1 []) (G₂ := latGens.getD 0 []) (List.subset_append_left _ _) t1 (by quickRfl)
theorem k5c1_0 : isLat7 C depth ((latGens.getD 1 [] ++ latGens.getD 0 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c1_0r z1 k1c1 t1
theorem k5c1_1r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 1 [] ++ latGens.getD 1 []).map code) depth) T1)
    (allL ((latGens.getD 1 [] ++ latGens.getD 1 []).map code) (memM 7 C (chainF C) T1)) = true :=
  recG_sub (G₁ := latGens.getD 1 []) (G₂ := latGens.getD 1 []) (List.Subset.refl _) t1 (by quickRfl)
theorem k5c1_1 : isLat7 C depth ((latGens.getD 1 [] ++ latGens.getD 1 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c1_1r z1 k1c1 t1
theorem k5c1_2a : setEqM (bfsM 7 C (chainF C) (((latGens.getD 1 []).eraseIdx 1 ++ [perm7 [[2, 3], [5, 6]]]).map code) depth) T6 = true := by quickRfl
theorem k5c1_2s : setEqM (bfsM 7 C (chainF C) ((latGens.getD 1 [] ++ [perm7 [[2, 3], [5, 6]]]).map code) depth) T6 = true :=
  recG_mono (G := (latGens.getD 1 []).eraseIdx 1 ++ [perm7 [[2, 3], [5, 6]]]) (G' := latGens.getD 1 [] ++ [perm7 [[2, 3], [5, 6]]]) (Z := latGens.getD 6 []) hok inj (eraseIdx_app_sub _ _ 1) k5c1_2a (by quickRfl) k1c6 t6
theorem k5c1_2r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 1 [] ++ latGens.getD 2 []).map code) depth) T6)
    (allL ((latGens.getD 1 [] ++ latGens.getD 2 []).map code) (memM 7 C (chainF C) T6)) = true :=
  recG_dup (G₁ := latGens.getD 1 []) (D := dGens) (N := [perm7 [[2, 3], [5, 6]]]) (List.subset_append_left _ _) k5c1_2s (by quickRfl)
theorem k5c1_2 : isLat7 C depth ((latGens.getD 1 [] ++ latGens.getD 2 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c1_2r z6 k1c6 t6
theorem k5c1_3a : setEqM (bfsM 7 C (chainF C) (((latGens.getD 1 []).eraseIdx 1 ++ [perm7 [[2, 3], [4, 5]]]).map code) depth) T6 = true := by quickRfl
theorem k5c1_3s : setEqM (bfsM 7 C (chainF C) ((latGens.getD 1 [] ++ [perm7 [[2, 3], [4, 5]]]).map code) depth) T6 = true :=
  recG_mono (G := (latGens.getD 1 []).eraseIdx 1 ++ [perm7 [[2, 3], [4, 5]]]) (G' := latGens.getD 1 [] ++ [perm7 [[2, 3], [4, 5]]]) (Z := latGens.getD 6 []) hok inj (eraseIdx_app_sub _ _ 1) k5c1_3a (by quickRfl) k1c6 t6
theorem k5c1_3r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 1 [] ++ latGens.getD 3 []).map code) depth) T6)
    (allL ((latGens.getD 1 [] ++ latGens.getD 3 []).map code) (memM 7 C (chainF C) T6)) = true :=
  recG_dup (G₁ := latGens.getD 1 []) (D := dGens) (N := [perm7 [[2, 3], [4, 5]]]) (List.subset_append_left _ _) k5c1_3s (by quickRfl)
theorem k5c1_3 : isLat7 C depth ((latGens.getD 1 [] ++ latGens.getD 3 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c1_3r z6 k1c6 t6
theorem k5c1_4a : setEqM (bfsM 7 C (chainF C) (((latGens.getD 1 []).eraseIdx 1 ++ [perm7 [[2, 3], [4, 6]]]).map code) depth) T6 = true := by quickRfl
theorem k5c1_4s : setEqM (bfsM 7 C (chainF C) ((latGens.getD 1 [] ++ [perm7 [[2, 3], [4, 6]]]).map code) depth) T6 = true :=
  recG_mono (G := (latGens.getD 1 []).eraseIdx 1 ++ [perm7 [[2, 3], [4, 6]]]) (G' := latGens.getD 1 [] ++ [perm7 [[2, 3], [4, 6]]]) (Z := latGens.getD 6 []) hok inj (eraseIdx_app_sub _ _ 1) k5c1_4a (by quickRfl) k1c6 t6
theorem k5c1_4r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 1 [] ++ latGens.getD 4 []).map code) depth) T6)
    (allL ((latGens.getD 1 [] ++ latGens.getD 4 []).map code) (memM 7 C (chainF C) T6)) = true :=
  recG_dup (G₁ := latGens.getD 1 []) (D := dGens) (N := [perm7 [[2, 3], [4, 6]]]) (List.subset_append_left _ _) k5c1_4s (by quickRfl)
theorem k5c1_4 : isLat7 C depth ((latGens.getD 1 [] ++ latGens.getD 4 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c1_4r z6 k1c6 t6
theorem k5c1_5s : setEqM (bfsM 7 C (chainF C) ((latGens.getD 1 [] ++ [perm7 [[1, 4], [3, 5]]]).map code) depth) T11 = true :=
  recG_ball (S := jS7) (m := 5) (k := 4) hok inj (by decide) jS7t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k5c1_5r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 1 [] ++ latGens.getD 5 []).map code) depth) T11)
    (allL ((latGens.getD 1 [] ++ latGens.getD 5 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_dup (G₁ := latGens.getD 1 []) (D := dGens) (N := [perm7 [[1, 4], [3, 5]]]) (List.subset_append_left _ _) k5c1_5s (by quickRfl)
theorem k5c1_5 : isLat7 C depth ((latGens.getD 1 [] ++ latGens.getD 5 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c1_5r z11 k1c11 t11
theorem k5c1_6r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 1 [] ++ latGens.getD 6 []).map code) depth) T6)
    (allL ((latGens.getD 1 [] ++ latGens.getD 6 []).map code) (memM 7 C (chainF C) T6)) = true :=
  recG_monoR (G := latGens.getD 6 []) (G' := latGens.getD 1 [] ++ latGens.getD 6 []) (Z := latGens.getD 6 []) hok inj (List.subset_append_right _ _) t6 (by quickRfl) k1c6 t6
theorem k5c1_6 : isLat7 C depth ((latGens.getD 1 [] ++ latGens.getD 6 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c1_6r z6 k1c6 t6
theorem k5c1_7s : setEqM (bfsM 7 C (chainF C) ((latGens.getD 1 [] ++ [perm7 [[3, 6], [4, 5]]]).map code) depth) T11 = true :=
  recG_ball (S := jS5) (m := 5) (k := 4) hok inj (by decide) jS5t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k5c1_7r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 1 [] ++ latGens.getD 7 []).map code) depth) T11)
    (allL ((latGens.getD 1 [] ++ latGens.getD 7 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_dup (G₁ := latGens.getD 1 []) (D := dGens) (N := [perm7 [[3, 6], [4, 5]]]) (List.subset_append_left _ _) k5c1_7s (by quickRfl)
theorem k5c1_7 : isLat7 C depth ((latGens.getD 1 [] ++ latGens.getD 7 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c1_7r z11 k1c11 t11
theorem k5c1_8s : setEqM (bfsM 7 C (chainF C) ((latGens.getD 1 [] ++ [perm7 [[2, 5], [3, 6]]]).map code) depth) T11 = true :=
  recG_ball (S := jS1) (m := 5) (k := 4) hok inj (by decide) jS1t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k5c1_8r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 1 [] ++ latGens.getD 8 []).map code) depth) T11)
    (allL ((latGens.getD 1 [] ++ latGens.getD 8 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_dup (G₁ := latGens.getD 1 []) (D := dGens) (N := [perm7 [[2, 5], [3, 6]]]) (List.subset_append_left _ _) k5c1_8s (by quickRfl)
theorem k5c1_8 : isLat7 C depth ((latGens.getD 1 [] ++ latGens.getD 8 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c1_8r z11 k1c11 t11
theorem k5c1_9s : setEqM (bfsM 7 C (chainF C) ((latGens.getD 1 [] ++ [perm7 [[2, 4], [3, 6]]]).map code) depth) T11 = true :=
  recG_ball (S := jS0) (m := 10) (k := 2) hok inj (by decide) jS0t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k5c1_9r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 1 [] ++ latGens.getD 9 []).map code) depth) T11)
    (allL ((latGens.getD 1 [] ++ latGens.getD 9 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_dup (G₁ := latGens.getD 1 []) (D := dGens) (N := [perm7 [[2, 4], [3, 6]]]) (List.subset_append_left _ _) k5c1_9s (by quickRfl)
theorem k5c1_9 : isLat7 C depth ((latGens.getD 1 [] ++ latGens.getD 9 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c1_9r z11 k1c11 t11
theorem k5c1_10s : setEqM (bfsM 7 C (chainF C) ((latGens.getD 1 [] ++ [perm7 [[3, 4, 5]]]).map code) depth) T11 = true :=
  recG_ball (S := jS5) (m := 5) (k := 4) hok inj (by decide) jS5t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k5c1_10r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 1 [] ++ latGens.getD 10 []).map code) depth) T11)
    (allL ((latGens.getD 1 [] ++ latGens.getD 10 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_dup (G₁ := latGens.getD 1 []) (D := dGens) (N := [perm7 [[3, 4, 5]]]) (List.subset_append_left _ _) k5c1_10s (by quickRfl)
theorem k5c1_10 : isLat7 C depth ((latGens.getD 1 [] ++ latGens.getD 10 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c1_10r z11 k1c11 t11
theorem k5c1_11r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 1 [] ++ latGens.getD 11 []).map code) depth) T11)
    (allL ((latGens.getD 1 [] ++ latGens.getD 11 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 11 []) (G' := latGens.getD 1 [] ++ latGens.getD 11 []) (Z := latGens.getD 11 []) hok inj (List.subset_append_right _ _) t11 (by quickRfl) k1c11 t11
theorem k5c1_11 : isLat7 C depth ((latGens.getD 1 [] ++ latGens.getD 11 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c1_11r z11 k1c11 t11
theorem k5c1 : allA latGens (fun G₂ => isLat7 C depth
    ((latGens.getD 1 [] ++ G₂).map code) (latGens.map (List.map code))) = true :=
  allA_of_getD latGens _ [] (fun j hj => match j, hj with
    | 0, _ => k5c1_0
    | 1, _ => k5c1_1
    | 2, _ => k5c1_2
    | 3, _ => k5c1_3
    | 4, _ => k5c1_4
    | 5, _ => k5c1_5
    | 6, _ => k5c1_6
    | 7, _ => k5c1_7
    | 8, _ => k5c1_8
    | 9, _ => k5c1_9
    | 10, _ => k5c1_10
    | 11, _ => k5c1_11
    | k + 12, h => absurd h (by
      have : latGens.length = 12 := rfl
      omega))
theorem k5c2_0r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 2 [] ++ latGens.getD 0 []).map code) depth) T2)
    (allL ((latGens.getD 2 [] ++ latGens.getD 0 []).map code) (memM 7 C (chainF C) T2)) = true :=
  recG_sub (G₁ := latGens.getD 2 []) (G₂ := latGens.getD 0 []) (List.subset_append_left _ _) t2 (by quickRfl)
theorem k5c2_0 : isLat7 C depth ((latGens.getD 2 [] ++ latGens.getD 0 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c2_0r z2 k1c2 t2
theorem k5c2_1r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 2 [] ++ latGens.getD 1 []).map code) depth) T6)
    (allL ((latGens.getD 2 [] ++ latGens.getD 1 []).map code) (memM 7 C (chainF C) T6)) = true :=
  recG_monoR (G := latGens.getD 1 [] ++ latGens.getD 2 []) (G' := latGens.getD 2 [] ++ latGens.getD 1 []) (Z := latGens.getD 6 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c1_2r) (by quickRfl) k1c6 t6
theorem k5c2_1 : isLat7 C depth ((latGens.getD 2 [] ++ latGens.getD 1 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c2_1r z6 k1c6 t6
theorem k5c2_2r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 2 [] ++ latGens.getD 2 []).map code) depth) T2)
    (allL ((latGens.getD 2 [] ++ latGens.getD 2 []).map code) (memM 7 C (chainF C) T2)) = true :=
  recG_sub (G₁ := latGens.getD 2 []) (G₂ := latGens.getD 2 []) (List.Subset.refl _) t2 (by quickRfl)
theorem k5c2_2 : isLat7 C depth ((latGens.getD 2 [] ++ latGens.getD 2 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c2_2r z2 k1c2 t2
theorem k5c2_3r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 2 [] ++ latGens.getD 3 []).map code) depth) T6)
    (allL ((latGens.getD 2 [] ++ latGens.getD 3 []).map code) (memM 7 C (chainF C) T6)) = true :=
  recG_monoR (G := latGens.getD 6 []) (G' := latGens.getD 2 [] ++ latGens.getD 3 []) (Z := latGens.getD 6 []) hok inj (sub_pair (D := dGens) (a := perm7 [[2, 3], [5, 6]]) (b := perm7 [[2, 3], [4, 5]])) t6 (by quickRfl) k1c6 t6
theorem k5c2_3 : isLat7 C depth ((latGens.getD 2 [] ++ latGens.getD 3 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c2_3r z6 k1c6 t6
theorem k5c2_4a : setEqM (bfsM 7 C (chainF C) (((latGens.getD 2 []).eraseIdx 1 ++ [perm7 [[2, 3], [4, 6]]]).map code) depth) T6 = true := by quickRfl
theorem k5c2_4s : setEqM (bfsM 7 C (chainF C) ((latGens.getD 2 [] ++ [perm7 [[2, 3], [4, 6]]]).map code) depth) T6 = true :=
  recG_mono (G := (latGens.getD 2 []).eraseIdx 1 ++ [perm7 [[2, 3], [4, 6]]]) (G' := latGens.getD 2 [] ++ [perm7 [[2, 3], [4, 6]]]) (Z := latGens.getD 6 []) hok inj (eraseIdx_app_sub _ _ 1) k5c2_4a (by quickRfl) k1c6 t6
theorem k5c2_4r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 2 [] ++ latGens.getD 4 []).map code) depth) T6)
    (allL ((latGens.getD 2 [] ++ latGens.getD 4 []).map code) (memM 7 C (chainF C) T6)) = true :=
  recG_dup (G₁ := latGens.getD 2 []) (D := dGens) (N := [perm7 [[2, 3], [4, 6]]]) (List.subset_append_left _ _) k5c2_4s (by quickRfl)
theorem k5c2_4 : isLat7 C depth ((latGens.getD 2 [] ++ latGens.getD 4 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c2_4r z6 k1c6 t6
theorem k5c2_5a : setEqM (bfsM 7 C (chainF C) (((latGens.getD 2 []).eraseIdx 1 ++ [perm7 [[1, 4], [3, 5]]]).map code) depth) T8 = true := by quickRfl
theorem k5c2_5s : setEqM (bfsM 7 C (chainF C) ((latGens.getD 2 [] ++ [perm7 [[1, 4], [3, 5]]]).map code) depth) T8 = true :=
  recG_mono (G := (latGens.getD 2 []).eraseIdx 1 ++ [perm7 [[1, 4], [3, 5]]]) (G' := latGens.getD 2 [] ++ [perm7 [[1, 4], [3, 5]]]) (Z := latGens.getD 8 []) hok inj (eraseIdx_app_sub _ _ 1) k5c2_5a (by quickRfl) k1c8 t8
theorem k5c2_5r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 2 [] ++ latGens.getD 5 []).map code) depth) T8)
    (allL ((latGens.getD 2 [] ++ latGens.getD 5 []).map code) (memM 7 C (chainF C) T8)) = true :=
  recG_dup (G₁ := latGens.getD 2 []) (D := dGens) (N := [perm7 [[1, 4], [3, 5]]]) (List.subset_append_left _ _) k5c2_5s (by quickRfl)
theorem k5c2_5 : isLat7 C depth ((latGens.getD 2 [] ++ latGens.getD 5 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c2_5r z8 k1c8 t8
theorem k5c2_6r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 2 [] ++ latGens.getD 6 []).map code) depth) T6)
    (allL ((latGens.getD 2 [] ++ latGens.getD 6 []).map code) (memM 7 C (chainF C) T6)) = true :=
  recG_monoR (G := latGens.getD 6 []) (G' := latGens.getD 2 [] ++ latGens.getD 6 []) (Z := latGens.getD 6 []) hok inj (List.subset_append_right _ _) t6 (by quickRfl) k1c6 t6
theorem k5c2_6 : isLat7 C depth ((latGens.getD 2 [] ++ latGens.getD 6 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c2_6r z6 k1c6 t6
theorem k5c2_7s : setEqM (bfsM 7 C (chainF C) ((latGens.getD 2 [] ++ [perm7 [[3, 6], [4, 5]]]).map code) depth) T11 = true :=
  recG_ball (S := jS3) (m := 10) (k := 2) hok inj (by decide) jS3t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k5c2_7r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 2 [] ++ latGens.getD 7 []).map code) depth) T11)
    (allL ((latGens.getD 2 [] ++ latGens.getD 7 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_dup (G₁ := latGens.getD 2 []) (D := dGens) (N := [perm7 [[3, 6], [4, 5]]]) (List.subset_append_left _ _) k5c2_7s (by quickRfl)
theorem k5c2_7 : isLat7 C depth ((latGens.getD 2 [] ++ latGens.getD 7 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c2_7r z11 k1c11 t11
theorem k5c2_8r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 2 [] ++ latGens.getD 8 []).map code) depth) T8)
    (allL ((latGens.getD 2 [] ++ latGens.getD 8 []).map code) (memM 7 C (chainF C) T8)) = true :=
  recG_monoR (G := latGens.getD 8 []) (G' := latGens.getD 2 [] ++ latGens.getD 8 []) (Z := latGens.getD 8 []) hok inj (List.subset_append_right _ _) t8 (by quickRfl) k1c8 t8
theorem k5c2_8 : isLat7 C depth ((latGens.getD 2 [] ++ latGens.getD 8 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c2_8r z8 k1c8 t8
theorem k5c2_9a : setEqM (bfsM 7 C (chainF C) (((latGens.getD 2 []).eraseIdx 1 ++ [perm7 [[2, 4], [3, 6]]]).map code) depth) T11 = true := by quickRfl
theorem k5c2_9s : setEqM (bfsM 7 C (chainF C) ((latGens.getD 2 [] ++ [perm7 [[2, 4], [3, 6]]]).map code) depth) T11 = true :=
  recG_mono (G := (latGens.getD 2 []).eraseIdx 1 ++ [perm7 [[2, 4], [3, 6]]]) (G' := latGens.getD 2 [] ++ [perm7 [[2, 4], [3, 6]]]) (Z := latGens.getD 11 []) hok inj (eraseIdx_app_sub _ _ 1) k5c2_9a (by quickRfl) k1c11 t11
theorem k5c2_9r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 2 [] ++ latGens.getD 9 []).map code) depth) T11)
    (allL ((latGens.getD 2 [] ++ latGens.getD 9 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_dup (G₁ := latGens.getD 2 []) (D := dGens) (N := [perm7 [[2, 4], [3, 6]]]) (List.subset_append_left _ _) k5c2_9s (by quickRfl)
theorem k5c2_9 : isLat7 C depth ((latGens.getD 2 [] ++ latGens.getD 9 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c2_9r z11 k1c11 t11
theorem k5c2_10s : setEqM (bfsM 7 C (chainF C) ((latGens.getD 2 [] ++ [perm7 [[3, 4, 5]]]).map code) depth) T11 = true :=
  recG_ball (S := jS6) (m := 5) (k := 4) hok inj (by decide) jS6t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k5c2_10r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 2 [] ++ latGens.getD 10 []).map code) depth) T11)
    (allL ((latGens.getD 2 [] ++ latGens.getD 10 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_dup (G₁ := latGens.getD 2 []) (D := dGens) (N := [perm7 [[3, 4, 5]]]) (List.subset_append_left _ _) k5c2_10s (by quickRfl)
theorem k5c2_10 : isLat7 C depth ((latGens.getD 2 [] ++ latGens.getD 10 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c2_10r z11 k1c11 t11
theorem k5c2_11r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 2 [] ++ latGens.getD 11 []).map code) depth) T11)
    (allL ((latGens.getD 2 [] ++ latGens.getD 11 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 11 []) (G' := latGens.getD 2 [] ++ latGens.getD 11 []) (Z := latGens.getD 11 []) hok inj (List.subset_append_right _ _) t11 (by quickRfl) k1c11 t11
theorem k5c2_11 : isLat7 C depth ((latGens.getD 2 [] ++ latGens.getD 11 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c2_11r z11 k1c11 t11
theorem k5c2 : allA latGens (fun G₂ => isLat7 C depth
    ((latGens.getD 2 [] ++ G₂).map code) (latGens.map (List.map code))) = true :=
  allA_of_getD latGens _ [] (fun j hj => match j, hj with
    | 0, _ => k5c2_0
    | 1, _ => k5c2_1
    | 2, _ => k5c2_2
    | 3, _ => k5c2_3
    | 4, _ => k5c2_4
    | 5, _ => k5c2_5
    | 6, _ => k5c2_6
    | 7, _ => k5c2_7
    | 8, _ => k5c2_8
    | 9, _ => k5c2_9
    | 10, _ => k5c2_10
    | 11, _ => k5c2_11
    | k + 12, h => absurd h (by
      have : latGens.length = 12 := rfl
      omega))
theorem k5c3_0r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 3 [] ++ latGens.getD 0 []).map code) depth) T3)
    (allL ((latGens.getD 3 [] ++ latGens.getD 0 []).map code) (memM 7 C (chainF C) T3)) = true :=
  recG_sub (G₁ := latGens.getD 3 []) (G₂ := latGens.getD 0 []) (List.subset_append_left _ _) t3 (by quickRfl)
theorem k5c3_0 : isLat7 C depth ((latGens.getD 3 [] ++ latGens.getD 0 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c3_0r z3 k1c3 t3
theorem k5c3_1r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 3 [] ++ latGens.getD 1 []).map code) depth) T6)
    (allL ((latGens.getD 3 [] ++ latGens.getD 1 []).map code) (memM 7 C (chainF C) T6)) = true :=
  recG_monoR (G := latGens.getD 1 [] ++ latGens.getD 3 []) (G' := latGens.getD 3 [] ++ latGens.getD 1 []) (Z := latGens.getD 6 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c1_3r) (by quickRfl) k1c6 t6
theorem k5c3_1 : isLat7 C depth ((latGens.getD 3 [] ++ latGens.getD 1 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c3_1r z6 k1c6 t6
theorem k5c3_2r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 3 [] ++ latGens.getD 2 []).map code) depth) T6)
    (allL ((latGens.getD 3 [] ++ latGens.getD 2 []).map code) (memM 7 C (chainF C) T6)) = true :=
  recG_monoR (G := latGens.getD 2 [] ++ latGens.getD 3 []) (G' := latGens.getD 3 [] ++ latGens.getD 2 []) (Z := latGens.getD 6 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c2_3r) (by quickRfl) k1c6 t6
theorem k5c3_2 : isLat7 C depth ((latGens.getD 3 [] ++ latGens.getD 2 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c3_2r z6 k1c6 t6
theorem k5c3_3r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 3 [] ++ latGens.getD 3 []).map code) depth) T3)
    (allL ((latGens.getD 3 [] ++ latGens.getD 3 []).map code) (memM 7 C (chainF C) T3)) = true :=
  recG_sub (G₁ := latGens.getD 3 []) (G₂ := latGens.getD 3 []) (List.Subset.refl _) t3 (by quickRfl)
theorem k5c3_3 : isLat7 C depth ((latGens.getD 3 [] ++ latGens.getD 3 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c3_3r z3 k1c3 t3
theorem k5c3_4a : setEqM (bfsM 7 C (chainF C) (((latGens.getD 3 []).eraseIdx 1 ++ [perm7 [[2, 3], [4, 6]]]).map code) depth) T6 = true := by quickRfl
theorem k5c3_4s : setEqM (bfsM 7 C (chainF C) ((latGens.getD 3 [] ++ [perm7 [[2, 3], [4, 6]]]).map code) depth) T6 = true :=
  recG_mono (G := (latGens.getD 3 []).eraseIdx 1 ++ [perm7 [[2, 3], [4, 6]]]) (G' := latGens.getD 3 [] ++ [perm7 [[2, 3], [4, 6]]]) (Z := latGens.getD 6 []) hok inj (eraseIdx_app_sub _ _ 1) k5c3_4a (by quickRfl) k1c6 t6
theorem k5c3_4r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 3 [] ++ latGens.getD 4 []).map code) depth) T6)
    (allL ((latGens.getD 3 [] ++ latGens.getD 4 []).map code) (memM 7 C (chainF C) T6)) = true :=
  recG_dup (G₁ := latGens.getD 3 []) (D := dGens) (N := [perm7 [[2, 3], [4, 6]]]) (List.subset_append_left _ _) k5c3_4s (by quickRfl)
theorem k5c3_4 : isLat7 C depth ((latGens.getD 3 [] ++ latGens.getD 4 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c3_4r z6 k1c6 t6
theorem k5c3_5a : setEqM (bfsM 7 C (chainF C) (((latGens.getD 3 []).eraseIdx 1 ++ [perm7 [[1, 4], [3, 5]]]).map code) depth) T10 = true := by quickRfl
theorem k5c3_5s : setEqM (bfsM 7 C (chainF C) ((latGens.getD 3 [] ++ [perm7 [[1, 4], [3, 5]]]).map code) depth) T10 = true :=
  recG_mono (G := (latGens.getD 3 []).eraseIdx 1 ++ [perm7 [[1, 4], [3, 5]]]) (G' := latGens.getD 3 [] ++ [perm7 [[1, 4], [3, 5]]]) (Z := latGens.getD 10 []) hok inj (eraseIdx_app_sub _ _ 1) k5c3_5a (by quickRfl) k1c10 t10
theorem k5c3_5r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 3 [] ++ latGens.getD 5 []).map code) depth) T10)
    (allL ((latGens.getD 3 [] ++ latGens.getD 5 []).map code) (memM 7 C (chainF C) T10)) = true :=
  recG_dup (G₁ := latGens.getD 3 []) (D := dGens) (N := [perm7 [[1, 4], [3, 5]]]) (List.subset_append_left _ _) k5c3_5s (by quickRfl)
theorem k5c3_5 : isLat7 C depth ((latGens.getD 3 [] ++ latGens.getD 5 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c3_5r z10 k1c10 t10
theorem k5c3_6r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 3 [] ++ latGens.getD 6 []).map code) depth) T6)
    (allL ((latGens.getD 3 [] ++ latGens.getD 6 []).map code) (memM 7 C (chainF C) T6)) = true :=
  recG_monoR (G := latGens.getD 6 []) (G' := latGens.getD 3 [] ++ latGens.getD 6 []) (Z := latGens.getD 6 []) hok inj (List.subset_append_right _ _) t6 (by quickRfl) k1c6 t6
theorem k5c3_6 : isLat7 C depth ((latGens.getD 3 [] ++ latGens.getD 6 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c3_6r z6 k1c6 t6
theorem k5c3_7r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 3 [] ++ latGens.getD 7 []).map code) depth) T7)
    (allL ((latGens.getD 3 [] ++ latGens.getD 7 []).map code) (memM 7 C (chainF C) T7)) = true :=
  recG_monoR (G := latGens.getD 7 []) (G' := latGens.getD 3 [] ++ latGens.getD 7 []) (Z := latGens.getD 7 []) hok inj (List.subset_append_right _ _) t7 (by quickRfl) k1c7 t7
theorem k5c3_7 : isLat7 C depth ((latGens.getD 3 [] ++ latGens.getD 7 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c3_7r z7 k1c7 t7
theorem k5c3_8s : setEqM (bfsM 7 C (chainF C) ((latGens.getD 3 [] ++ [perm7 [[2, 5], [3, 6]]]).map code) depth) T11 = true :=
  recG_ball (S := jS0) (m := 10) (k := 2) hok inj (by decide) jS0t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k5c3_8r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 3 [] ++ latGens.getD 8 []).map code) depth) T11)
    (allL ((latGens.getD 3 [] ++ latGens.getD 8 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_dup (G₁ := latGens.getD 3 []) (D := dGens) (N := [perm7 [[2, 5], [3, 6]]]) (List.subset_append_left _ _) k5c3_8s (by quickRfl)
theorem k5c3_8 : isLat7 C depth ((latGens.getD 3 [] ++ latGens.getD 8 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c3_8r z11 k1c11 t11
theorem k5c3_9s : setEqM (bfsM 7 C (chainF C) ((latGens.getD 3 [] ++ [perm7 [[2, 4], [3, 6]]]).map code) depth) T11 = true :=
  recG_ball (S := jS1) (m := 5) (k := 4) hok inj (by decide) jS1t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k5c3_9r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 3 [] ++ latGens.getD 9 []).map code) depth) T11)
    (allL ((latGens.getD 3 [] ++ latGens.getD 9 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_dup (G₁ := latGens.getD 3 []) (D := dGens) (N := [perm7 [[2, 4], [3, 6]]]) (List.subset_append_left _ _) k5c3_9s (by quickRfl)
theorem k5c3_9 : isLat7 C depth ((latGens.getD 3 [] ++ latGens.getD 9 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c3_9r z11 k1c11 t11
theorem k5c3_10r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 3 [] ++ latGens.getD 10 []).map code) depth) T10)
    (allL ((latGens.getD 3 [] ++ latGens.getD 10 []).map code) (memM 7 C (chainF C) T10)) = true :=
  recG_monoR (G := latGens.getD 10 []) (G' := latGens.getD 3 [] ++ latGens.getD 10 []) (Z := latGens.getD 10 []) hok inj (List.subset_append_right _ _) t10 (by quickRfl) k1c10 t10
theorem k5c3_10 : isLat7 C depth ((latGens.getD 3 [] ++ latGens.getD 10 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c3_10r z10 k1c10 t10
theorem k5c3_11r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 3 [] ++ latGens.getD 11 []).map code) depth) T11)
    (allL ((latGens.getD 3 [] ++ latGens.getD 11 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 11 []) (G' := latGens.getD 3 [] ++ latGens.getD 11 []) (Z := latGens.getD 11 []) hok inj (List.subset_append_right _ _) t11 (by quickRfl) k1c11 t11
theorem k5c3_11 : isLat7 C depth ((latGens.getD 3 [] ++ latGens.getD 11 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c3_11r z11 k1c11 t11
theorem k5c3 : allA latGens (fun G₂ => isLat7 C depth
    ((latGens.getD 3 [] ++ G₂).map code) (latGens.map (List.map code))) = true :=
  allA_of_getD latGens _ [] (fun j hj => match j, hj with
    | 0, _ => k5c3_0
    | 1, _ => k5c3_1
    | 2, _ => k5c3_2
    | 3, _ => k5c3_3
    | 4, _ => k5c3_4
    | 5, _ => k5c3_5
    | 6, _ => k5c3_6
    | 7, _ => k5c3_7
    | 8, _ => k5c3_8
    | 9, _ => k5c3_9
    | 10, _ => k5c3_10
    | 11, _ => k5c3_11
    | k + 12, h => absurd h (by
      have : latGens.length = 12 := rfl
      omega))
theorem k5c4_0r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 4 [] ++ latGens.getD 0 []).map code) depth) T4)
    (allL ((latGens.getD 4 [] ++ latGens.getD 0 []).map code) (memM 7 C (chainF C) T4)) = true :=
  recG_sub (G₁ := latGens.getD 4 []) (G₂ := latGens.getD 0 []) (List.subset_append_left _ _) t4 (by quickRfl)
theorem k5c4_0 : isLat7 C depth ((latGens.getD 4 [] ++ latGens.getD 0 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c4_0r z4 k1c4 t4
theorem k5c4_1r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 4 [] ++ latGens.getD 1 []).map code) depth) T6)
    (allL ((latGens.getD 4 [] ++ latGens.getD 1 []).map code) (memM 7 C (chainF C) T6)) = true :=
  recG_monoR (G := latGens.getD 1 [] ++ latGens.getD 4 []) (G' := latGens.getD 4 [] ++ latGens.getD 1 []) (Z := latGens.getD 6 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c1_4r) (by quickRfl) k1c6 t6
theorem k5c4_1 : isLat7 C depth ((latGens.getD 4 [] ++ latGens.getD 1 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c4_1r z6 k1c6 t6
theorem k5c4_2r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 4 [] ++ latGens.getD 2 []).map code) depth) T6)
    (allL ((latGens.getD 4 [] ++ latGens.getD 2 []).map code) (memM 7 C (chainF C) T6)) = true :=
  recG_monoR (G := latGens.getD 2 [] ++ latGens.getD 4 []) (G' := latGens.getD 4 [] ++ latGens.getD 2 []) (Z := latGens.getD 6 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c2_4r) (by quickRfl) k1c6 t6
theorem k5c4_2 : isLat7 C depth ((latGens.getD 4 [] ++ latGens.getD 2 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c4_2r z6 k1c6 t6
theorem k5c4_3r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 4 [] ++ latGens.getD 3 []).map code) depth) T6)
    (allL ((latGens.getD 4 [] ++ latGens.getD 3 []).map code) (memM 7 C (chainF C) T6)) = true :=
  recG_monoR (G := latGens.getD 3 [] ++ latGens.getD 4 []) (G' := latGens.getD 4 [] ++ latGens.getD 3 []) (Z := latGens.getD 6 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c3_4r) (by quickRfl) k1c6 t6
theorem k5c4_3 : isLat7 C depth ((latGens.getD 4 [] ++ latGens.getD 3 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c4_3r z6 k1c6 t6
theorem k5c4_4r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 4 [] ++ latGens.getD 4 []).map code) depth) T4)
    (allL ((latGens.getD 4 [] ++ latGens.getD 4 []).map code) (memM 7 C (chainF C) T4)) = true :=
  recG_sub (G₁ := latGens.getD 4 []) (G₂ := latGens.getD 4 []) (List.Subset.refl _) t4 (by quickRfl)
theorem k5c4_4 : isLat7 C depth ((latGens.getD 4 [] ++ latGens.getD 4 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c4_4r z4 k1c4 t4
theorem k5c4_5a : setEqM (bfsM 7 C (chainF C) (((latGens.getD 4 []).eraseIdx 1 ++ [perm7 [[1, 4], [3, 5]]]).map code) depth) T9 = true := by quickRfl
theorem k5c4_5s : setEqM (bfsM 7 C (chainF C) ((latGens.getD 4 [] ++ [perm7 [[1, 4], [3, 5]]]).map code) depth) T9 = true :=
  recG_mono (G := (latGens.getD 4 []).eraseIdx 1 ++ [perm7 [[1, 4], [3, 5]]]) (G' := latGens.getD 4 [] ++ [perm7 [[1, 4], [3, 5]]]) (Z := latGens.getD 9 []) hok inj (eraseIdx_app_sub _ _ 1) k5c4_5a (by quickRfl) k1c9 t9
theorem k5c4_5r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 4 [] ++ latGens.getD 5 []).map code) depth) T9)
    (allL ((latGens.getD 4 [] ++ latGens.getD 5 []).map code) (memM 7 C (chainF C) T9)) = true :=
  recG_dup (G₁ := latGens.getD 4 []) (D := dGens) (N := [perm7 [[1, 4], [3, 5]]]) (List.subset_append_left _ _) k5c4_5s (by quickRfl)
theorem k5c4_5 : isLat7 C depth ((latGens.getD 4 [] ++ latGens.getD 5 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c4_5r z9 k1c9 t9
theorem k5c4_6r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 4 [] ++ latGens.getD 6 []).map code) depth) T6)
    (allL ((latGens.getD 4 [] ++ latGens.getD 6 []).map code) (memM 7 C (chainF C) T6)) = true :=
  recG_monoR (G := latGens.getD 6 []) (G' := latGens.getD 4 [] ++ latGens.getD 6 []) (Z := latGens.getD 6 []) hok inj (List.subset_append_right _ _) t6 (by quickRfl) k1c6 t6
theorem k5c4_6 : isLat7 C depth ((latGens.getD 4 [] ++ latGens.getD 6 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c4_6r z6 k1c6 t6
theorem k5c4_7s : setEqM (bfsM 7 C (chainF C) ((latGens.getD 4 [] ++ [perm7 [[3, 6], [4, 5]]]).map code) depth) T11 = true :=
  recG_ball (S := jS4) (m := 10) (k := 2) hok inj (by decide) jS4t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k5c4_7r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 4 [] ++ latGens.getD 7 []).map code) depth) T11)
    (allL ((latGens.getD 4 [] ++ latGens.getD 7 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_dup (G₁ := latGens.getD 4 []) (D := dGens) (N := [perm7 [[3, 6], [4, 5]]]) (List.subset_append_left _ _) k5c4_7s (by quickRfl)
theorem k5c4_7 : isLat7 C depth ((latGens.getD 4 [] ++ latGens.getD 7 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c4_7r z11 k1c11 t11
theorem k5c4_8s : setEqM (bfsM 7 C (chainF C) ((latGens.getD 4 [] ++ [perm7 [[2, 5], [3, 6]]]).map code) depth) T11 = true :=
  recG_ball (S := jS8) (m := 10) (k := 2) hok inj (by decide) jS8t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k5c4_8r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 4 [] ++ latGens.getD 8 []).map code) depth) T11)
    (allL ((latGens.getD 4 [] ++ latGens.getD 8 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_dup (G₁ := latGens.getD 4 []) (D := dGens) (N := [perm7 [[2, 5], [3, 6]]]) (List.subset_append_left _ _) k5c4_8s (by quickRfl)
theorem k5c4_8 : isLat7 C depth ((latGens.getD 4 [] ++ latGens.getD 8 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c4_8r z11 k1c11 t11
theorem k5c4_9r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 4 [] ++ latGens.getD 9 []).map code) depth) T9)
    (allL ((latGens.getD 4 [] ++ latGens.getD 9 []).map code) (memM 7 C (chainF C) T9)) = true :=
  recG_monoR (G := latGens.getD 9 []) (G' := latGens.getD 4 [] ++ latGens.getD 9 []) (Z := latGens.getD 9 []) hok inj (List.subset_append_right _ _) t9 (by quickRfl) k1c9 t9
theorem k5c4_9 : isLat7 C depth ((latGens.getD 4 [] ++ latGens.getD 9 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c4_9r z9 k1c9 t9
theorem k5c4_10s : setEqM (bfsM 7 C (chainF C) ((latGens.getD 4 [] ++ [perm7 [[3, 4, 5]]]).map code) depth) T11 = true :=
  recG_ball (S := jS2) (m := 10) (k := 2) hok inj (by decide) jS2t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k5c4_10r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 4 [] ++ latGens.getD 10 []).map code) depth) T11)
    (allL ((latGens.getD 4 [] ++ latGens.getD 10 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_dup (G₁ := latGens.getD 4 []) (D := dGens) (N := [perm7 [[3, 4, 5]]]) (List.subset_append_left _ _) k5c4_10s (by quickRfl)
theorem k5c4_10 : isLat7 C depth ((latGens.getD 4 [] ++ latGens.getD 10 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c4_10r z11 k1c11 t11
theorem k5c4_11r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 4 [] ++ latGens.getD 11 []).map code) depth) T11)
    (allL ((latGens.getD 4 [] ++ latGens.getD 11 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 11 []) (G' := latGens.getD 4 [] ++ latGens.getD 11 []) (Z := latGens.getD 11 []) hok inj (List.subset_append_right _ _) t11 (by quickRfl) k1c11 t11
theorem k5c4_11 : isLat7 C depth ((latGens.getD 4 [] ++ latGens.getD 11 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c4_11r z11 k1c11 t11
theorem k5c4 : allA latGens (fun G₂ => isLat7 C depth
    ((latGens.getD 4 [] ++ G₂).map code) (latGens.map (List.map code))) = true :=
  allA_of_getD latGens _ [] (fun j hj => match j, hj with
    | 0, _ => k5c4_0
    | 1, _ => k5c4_1
    | 2, _ => k5c4_2
    | 3, _ => k5c4_3
    | 4, _ => k5c4_4
    | 5, _ => k5c4_5
    | 6, _ => k5c4_6
    | 7, _ => k5c4_7
    | 8, _ => k5c4_8
    | 9, _ => k5c4_9
    | 10, _ => k5c4_10
    | 11, _ => k5c4_11
    | k + 12, h => absurd h (by
      have : latGens.length = 12 := rfl
      omega))
theorem k5c5_0r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 5 [] ++ latGens.getD 0 []).map code) depth) T5)
    (allL ((latGens.getD 5 [] ++ latGens.getD 0 []).map code) (memM 7 C (chainF C) T5)) = true :=
  recG_sub (G₁ := latGens.getD 5 []) (G₂ := latGens.getD 0 []) (List.subset_append_left _ _) t5 (by quickRfl)
theorem k5c5_0 : isLat7 C depth ((latGens.getD 5 [] ++ latGens.getD 0 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c5_0r z5 k1c5 t5
theorem k5c5_1r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 5 [] ++ latGens.getD 1 []).map code) depth) T11)
    (allL ((latGens.getD 5 [] ++ latGens.getD 1 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 1 [] ++ latGens.getD 5 []) (G' := latGens.getD 5 [] ++ latGens.getD 1 []) (Z := latGens.getD 11 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c1_5r) (by quickRfl) k1c11 t11
theorem k5c5_1 : isLat7 C depth ((latGens.getD 5 [] ++ latGens.getD 1 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c5_1r z11 k1c11 t11
theorem k5c5_2r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 5 [] ++ latGens.getD 2 []).map code) depth) T8)
    (allL ((latGens.getD 5 [] ++ latGens.getD 2 []).map code) (memM 7 C (chainF C) T8)) = true :=
  recG_monoR (G := latGens.getD 2 [] ++ latGens.getD 5 []) (G' := latGens.getD 5 [] ++ latGens.getD 2 []) (Z := latGens.getD 8 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c2_5r) (by quickRfl) k1c8 t8
theorem k5c5_2 : isLat7 C depth ((latGens.getD 5 [] ++ latGens.getD 2 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c5_2r z8 k1c8 t8
theorem k5c5_3r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 5 [] ++ latGens.getD 3 []).map code) depth) T10)
    (allL ((latGens.getD 5 [] ++ latGens.getD 3 []).map code) (memM 7 C (chainF C) T10)) = true :=
  recG_monoR (G := latGens.getD 3 [] ++ latGens.getD 5 []) (G' := latGens.getD 5 [] ++ latGens.getD 3 []) (Z := latGens.getD 10 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c3_5r) (by quickRfl) k1c10 t10
theorem k5c5_3 : isLat7 C depth ((latGens.getD 5 [] ++ latGens.getD 3 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c5_3r z10 k1c10 t10
theorem k5c5_4r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 5 [] ++ latGens.getD 4 []).map code) depth) T9)
    (allL ((latGens.getD 5 [] ++ latGens.getD 4 []).map code) (memM 7 C (chainF C) T9)) = true :=
  recG_monoR (G := latGens.getD 4 [] ++ latGens.getD 5 []) (G' := latGens.getD 5 [] ++ latGens.getD 4 []) (Z := latGens.getD 9 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c4_5r) (by quickRfl) k1c9 t9
theorem k5c5_4 : isLat7 C depth ((latGens.getD 5 [] ++ latGens.getD 4 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c5_4r z9 k1c9 t9
theorem k5c5_5r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 5 [] ++ latGens.getD 5 []).map code) depth) T5)
    (allL ((latGens.getD 5 [] ++ latGens.getD 5 []).map code) (memM 7 C (chainF C) T5)) = true :=
  recG_sub (G₁ := latGens.getD 5 []) (G₂ := latGens.getD 5 []) (List.Subset.refl _) t5 (by quickRfl)
theorem k5c5_5 : isLat7 C depth ((latGens.getD 5 [] ++ latGens.getD 5 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c5_5r z5 k1c5 t5
theorem k5c5_6a : setEqM (bfsM 7 C (chainF C) (((latGens.getD 5 []).eraseIdx 1 ++ [perm7 [[2, 3], [4, 5]], perm7 [[2, 3], [5, 6]]]).map code) depth) T11 = true := by quickRfl
theorem k5c5_6s : setEqM (bfsM 7 C (chainF C) ((latGens.getD 5 [] ++ [perm7 [[2, 3], [4, 5]], perm7 [[2, 3], [5, 6]]]).map code) depth) T11 = true :=
  recG_mono (G := (latGens.getD 5 []).eraseIdx 1 ++ [perm7 [[2, 3], [4, 5]], perm7 [[2, 3], [5, 6]]]) (G' := latGens.getD 5 [] ++ [perm7 [[2, 3], [4, 5]], perm7 [[2, 3], [5, 6]]]) (Z := latGens.getD 11 []) hok inj (eraseIdx_app_sub _ _ 1) k5c5_6a (by quickRfl) k1c11 t11
theorem k5c5_6r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 5 [] ++ latGens.getD 6 []).map code) depth) T11)
    (allL ((latGens.getD 5 [] ++ latGens.getD 6 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_dup (G₁ := latGens.getD 5 []) (D := dGens) (N := [perm7 [[2, 3], [4, 5]], perm7 [[2, 3], [5, 6]]]) (List.subset_append_left _ _) k5c5_6s (by quickRfl)
theorem k5c5_6 : isLat7 C depth ((latGens.getD 5 [] ++ latGens.getD 6 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c5_6r z11 k1c11 t11
theorem k5c5_7s : setEqM (bfsM 7 C (chainF C) ((latGens.getD 5 [] ++ [perm7 [[3, 6], [4, 5]]]).map code) depth) T11 = true :=
  recG_ball (S := jS7) (m := 5) (k := 4) hok inj (by decide) jS7t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k5c5_7r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 5 [] ++ latGens.getD 7 []).map code) depth) T11)
    (allL ((latGens.getD 5 [] ++ latGens.getD 7 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_dup (G₁ := latGens.getD 5 []) (D := dGens) (N := [perm7 [[3, 6], [4, 5]]]) (List.subset_append_left _ _) k5c5_7s (by quickRfl)
theorem k5c5_7 : isLat7 C depth ((latGens.getD 5 [] ++ latGens.getD 7 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c5_7r z11 k1c11 t11
theorem k5c5_8r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 5 [] ++ latGens.getD 8 []).map code) depth) T8)
    (allL ((latGens.getD 5 [] ++ latGens.getD 8 []).map code) (memM 7 C (chainF C) T8)) = true :=
  recG_monoR (G := latGens.getD 8 []) (G' := latGens.getD 5 [] ++ latGens.getD 8 []) (Z := latGens.getD 8 []) hok inj (List.subset_append_right _ _) t8 (by quickRfl) k1c8 t8
theorem k5c5_8 : isLat7 C depth ((latGens.getD 5 [] ++ latGens.getD 8 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c5_8r z8 k1c8 t8
theorem k5c5_9r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 5 [] ++ latGens.getD 9 []).map code) depth) T9)
    (allL ((latGens.getD 5 [] ++ latGens.getD 9 []).map code) (memM 7 C (chainF C) T9)) = true :=
  recG_monoR (G := latGens.getD 9 []) (G' := latGens.getD 5 [] ++ latGens.getD 9 []) (Z := latGens.getD 9 []) hok inj (List.subset_append_right _ _) t9 (by quickRfl) k1c9 t9
theorem k5c5_9 : isLat7 C depth ((latGens.getD 5 [] ++ latGens.getD 9 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c5_9r z9 k1c9 t9
theorem k5c5_10r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 5 [] ++ latGens.getD 10 []).map code) depth) T10)
    (allL ((latGens.getD 5 [] ++ latGens.getD 10 []).map code) (memM 7 C (chainF C) T10)) = true :=
  recG_monoR (G := latGens.getD 10 []) (G' := latGens.getD 5 [] ++ latGens.getD 10 []) (Z := latGens.getD 10 []) hok inj (List.subset_append_right _ _) t10 (by quickRfl) k1c10 t10
theorem k5c5_10 : isLat7 C depth ((latGens.getD 5 [] ++ latGens.getD 10 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c5_10r z10 k1c10 t10
theorem k5c5_11r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 5 [] ++ latGens.getD 11 []).map code) depth) T11)
    (allL ((latGens.getD 5 [] ++ latGens.getD 11 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 11 []) (G' := latGens.getD 5 [] ++ latGens.getD 11 []) (Z := latGens.getD 11 []) hok inj (List.subset_append_right _ _) t11 (by quickRfl) k1c11 t11
theorem k5c5_11 : isLat7 C depth ((latGens.getD 5 [] ++ latGens.getD 11 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c5_11r z11 k1c11 t11
theorem k5c5 : allA latGens (fun G₂ => isLat7 C depth
    ((latGens.getD 5 [] ++ G₂).map code) (latGens.map (List.map code))) = true :=
  allA_of_getD latGens _ [] (fun j hj => match j, hj with
    | 0, _ => k5c5_0
    | 1, _ => k5c5_1
    | 2, _ => k5c5_2
    | 3, _ => k5c5_3
    | 4, _ => k5c5_4
    | 5, _ => k5c5_5
    | 6, _ => k5c5_6
    | 7, _ => k5c5_7
    | 8, _ => k5c5_8
    | 9, _ => k5c5_9
    | 10, _ => k5c5_10
    | 11, _ => k5c5_11
    | k + 12, h => absurd h (by
      have : latGens.length = 12 := rfl
      omega))
theorem k5c6_0r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 6 [] ++ latGens.getD 0 []).map code) depth) T6)
    (allL ((latGens.getD 6 [] ++ latGens.getD 0 []).map code) (memM 7 C (chainF C) T6)) = true :=
  recG_sub (G₁ := latGens.getD 6 []) (G₂ := latGens.getD 0 []) (List.subset_append_left _ _) t6 (by quickRfl)
theorem k5c6_0 : isLat7 C depth ((latGens.getD 6 [] ++ latGens.getD 0 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c6_0r z6 k1c6 t6
theorem k5c6_1r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 6 [] ++ latGens.getD 1 []).map code) depth) T6)
    (allL ((latGens.getD 6 [] ++ latGens.getD 1 []).map code) (memM 7 C (chainF C) T6)) = true :=
  recG_monoR (G := latGens.getD 6 []) (G' := latGens.getD 6 [] ++ latGens.getD 1 []) (Z := latGens.getD 6 []) hok inj (List.subset_append_left _ _) t6 (by quickRfl) k1c6 t6
theorem k5c6_1 : isLat7 C depth ((latGens.getD 6 [] ++ latGens.getD 1 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c6_1r z6 k1c6 t6
theorem k5c6_2r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 6 [] ++ latGens.getD 2 []).map code) depth) T6)
    (allL ((latGens.getD 6 [] ++ latGens.getD 2 []).map code) (memM 7 C (chainF C) T6)) = true :=
  recG_monoR (G := latGens.getD 6 []) (G' := latGens.getD 6 [] ++ latGens.getD 2 []) (Z := latGens.getD 6 []) hok inj (List.subset_append_left _ _) t6 (by quickRfl) k1c6 t6
theorem k5c6_2 : isLat7 C depth ((latGens.getD 6 [] ++ latGens.getD 2 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c6_2r z6 k1c6 t6
theorem k5c6_3r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 6 [] ++ latGens.getD 3 []).map code) depth) T6)
    (allL ((latGens.getD 6 [] ++ latGens.getD 3 []).map code) (memM 7 C (chainF C) T6)) = true :=
  recG_monoR (G := latGens.getD 6 []) (G' := latGens.getD 6 [] ++ latGens.getD 3 []) (Z := latGens.getD 6 []) hok inj (List.subset_append_left _ _) t6 (by quickRfl) k1c6 t6
theorem k5c6_3 : isLat7 C depth ((latGens.getD 6 [] ++ latGens.getD 3 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c6_3r z6 k1c6 t6
theorem k5c6_4r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 6 [] ++ latGens.getD 4 []).map code) depth) T6)
    (allL ((latGens.getD 6 [] ++ latGens.getD 4 []).map code) (memM 7 C (chainF C) T6)) = true :=
  recG_monoR (G := latGens.getD 6 []) (G' := latGens.getD 6 [] ++ latGens.getD 4 []) (Z := latGens.getD 6 []) hok inj (List.subset_append_left _ _) t6 (by quickRfl) k1c6 t6
theorem k5c6_4 : isLat7 C depth ((latGens.getD 6 [] ++ latGens.getD 4 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c6_4r z6 k1c6 t6
theorem k5c6_5r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 6 [] ++ latGens.getD 5 []).map code) depth) T11)
    (allL ((latGens.getD 6 [] ++ latGens.getD 5 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 5 [] ++ latGens.getD 6 []) (G' := latGens.getD 6 [] ++ latGens.getD 5 []) (Z := latGens.getD 11 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c5_6r) (by quickRfl) k1c11 t11
theorem k5c6_5 : isLat7 C depth ((latGens.getD 6 [] ++ latGens.getD 5 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c6_5r z11 k1c11 t11
theorem k5c6_6r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 6 [] ++ latGens.getD 6 []).map code) depth) T6)
    (allL ((latGens.getD 6 [] ++ latGens.getD 6 []).map code) (memM 7 C (chainF C) T6)) = true :=
  recG_sub (G₁ := latGens.getD 6 []) (G₂ := latGens.getD 6 []) (List.Subset.refl _) t6 (by quickRfl)
theorem k5c6_6 : isLat7 C depth ((latGens.getD 6 [] ++ latGens.getD 6 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c6_6r z6 k1c6 t6
theorem k5c6_7r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 6 [] ++ latGens.getD 7 []).map code) depth) T11)
    (allL ((latGens.getD 6 [] ++ latGens.getD 7 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 2 [] ++ latGens.getD 7 []) (G' := latGens.getD 6 [] ++ latGens.getD 7 []) (Z := latGens.getD 11 []) hok inj (sub_mid (D := dGens) (A := [perm7 [[2, 3], [5, 6]]]) (B := [perm7 [[2, 3], [4, 5]], perm7 [[2, 3], [5, 6]]]) (X := latGens.getD 7 []) (List.subset_cons_self _ _)) (setEqM_of_recR k5c2_7r) (by quickRfl) k1c11 t11
theorem k5c6_7 : isLat7 C depth ((latGens.getD 6 [] ++ latGens.getD 7 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c6_7r z11 k1c11 t11
theorem k5c6_8r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 6 [] ++ latGens.getD 8 []).map code) depth) T11)
    (allL ((latGens.getD 6 [] ++ latGens.getD 8 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 3 [] ++ latGens.getD 8 []) (G' := latGens.getD 6 [] ++ latGens.getD 8 []) (Z := latGens.getD 11 []) hok inj (sub_mid (D := dGens) (A := [perm7 [[2, 3], [4, 5]]]) (B := [perm7 [[2, 3], [4, 5]], perm7 [[2, 3], [5, 6]]]) (X := latGens.getD 8 []) (List.cons_subset_cons _ (List.nil_subset _))) (setEqM_of_recR k5c3_8r) (by quickRfl) k1c11 t11
theorem k5c6_8 : isLat7 C depth ((latGens.getD 6 [] ++ latGens.getD 8 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c6_8r z11 k1c11 t11
theorem k5c6_9r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 6 [] ++ latGens.getD 9 []).map code) depth) T11)
    (allL ((latGens.getD 6 [] ++ latGens.getD 9 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 2 [] ++ latGens.getD 9 []) (G' := latGens.getD 6 [] ++ latGens.getD 9 []) (Z := latGens.getD 11 []) hok inj (sub_mid (D := dGens) (A := [perm7 [[2, 3], [5, 6]]]) (B := [perm7 [[2, 3], [4, 5]], perm7 [[2, 3], [5, 6]]]) (X := latGens.getD 9 []) (List.subset_cons_self _ _)) (setEqM_of_recR k5c2_9r) (by quickRfl) k1c11 t11
theorem k5c6_9 : isLat7 C depth ((latGens.getD 6 [] ++ latGens.getD 9 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c6_9r z11 k1c11 t11
theorem k5c6_10r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 6 [] ++ latGens.getD 10 []).map code) depth) T11)
    (allL ((latGens.getD 6 [] ++ latGens.getD 10 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 2 [] ++ latGens.getD 10 []) (G' := latGens.getD 6 [] ++ latGens.getD 10 []) (Z := latGens.getD 11 []) hok inj (sub_mid (D := dGens) (A := [perm7 [[2, 3], [5, 6]]]) (B := [perm7 [[2, 3], [4, 5]], perm7 [[2, 3], [5, 6]]]) (X := latGens.getD 10 []) (List.subset_cons_self _ _)) (setEqM_of_recR k5c2_10r) (by quickRfl) k1c11 t11
theorem k5c6_10 : isLat7 C depth ((latGens.getD 6 [] ++ latGens.getD 10 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c6_10r z11 k1c11 t11
theorem k5c6_11r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 6 [] ++ latGens.getD 11 []).map code) depth) T11)
    (allL ((latGens.getD 6 [] ++ latGens.getD 11 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 11 []) (G' := latGens.getD 6 [] ++ latGens.getD 11 []) (Z := latGens.getD 11 []) hok inj (List.subset_append_right _ _) t11 (by quickRfl) k1c11 t11
theorem k5c6_11 : isLat7 C depth ((latGens.getD 6 [] ++ latGens.getD 11 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c6_11r z11 k1c11 t11
theorem k5c6 : allA latGens (fun G₂ => isLat7 C depth
    ((latGens.getD 6 [] ++ G₂).map code) (latGens.map (List.map code))) = true :=
  allA_of_getD latGens _ [] (fun j hj => match j, hj with
    | 0, _ => k5c6_0
    | 1, _ => k5c6_1
    | 2, _ => k5c6_2
    | 3, _ => k5c6_3
    | 4, _ => k5c6_4
    | 5, _ => k5c6_5
    | 6, _ => k5c6_6
    | 7, _ => k5c6_7
    | 8, _ => k5c6_8
    | 9, _ => k5c6_9
    | 10, _ => k5c6_10
    | 11, _ => k5c6_11
    | k + 12, h => absurd h (by
      have : latGens.length = 12 := rfl
      omega))
theorem k5c7_0r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 7 [] ++ latGens.getD 0 []).map code) depth) T7)
    (allL ((latGens.getD 7 [] ++ latGens.getD 0 []).map code) (memM 7 C (chainF C) T7)) = true :=
  recG_sub (G₁ := latGens.getD 7 []) (G₂ := latGens.getD 0 []) (List.subset_append_left _ _) t7 (by quickRfl)
theorem k5c7_0 : isLat7 C depth ((latGens.getD 7 [] ++ latGens.getD 0 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c7_0r z7 k1c7 t7
theorem k5c7_1r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 7 [] ++ latGens.getD 1 []).map code) depth) T11)
    (allL ((latGens.getD 7 [] ++ latGens.getD 1 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 1 [] ++ latGens.getD 7 []) (G' := latGens.getD 7 [] ++ latGens.getD 1 []) (Z := latGens.getD 11 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c1_7r) (by quickRfl) k1c11 t11
theorem k5c7_1 : isLat7 C depth ((latGens.getD 7 [] ++ latGens.getD 1 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c7_1r z11 k1c11 t11
theorem k5c7_2r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 7 [] ++ latGens.getD 2 []).map code) depth) T11)
    (allL ((latGens.getD 7 [] ++ latGens.getD 2 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 2 [] ++ latGens.getD 7 []) (G' := latGens.getD 7 [] ++ latGens.getD 2 []) (Z := latGens.getD 11 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c2_7r) (by quickRfl) k1c11 t11
theorem k5c7_2 : isLat7 C depth ((latGens.getD 7 [] ++ latGens.getD 2 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c7_2r z11 k1c11 t11
theorem k5c7_3r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 7 [] ++ latGens.getD 3 []).map code) depth) T7)
    (allL ((latGens.getD 7 [] ++ latGens.getD 3 []).map code) (memM 7 C (chainF C) T7)) = true :=
  recG_monoR (G := latGens.getD 7 []) (G' := latGens.getD 7 [] ++ latGens.getD 3 []) (Z := latGens.getD 7 []) hok inj (List.subset_append_left _ _) t7 (by quickRfl) k1c7 t7
theorem k5c7_3 : isLat7 C depth ((latGens.getD 7 [] ++ latGens.getD 3 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c7_3r z7 k1c7 t7
theorem k5c7_4r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 7 [] ++ latGens.getD 4 []).map code) depth) T11)
    (allL ((latGens.getD 7 [] ++ latGens.getD 4 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 4 [] ++ latGens.getD 7 []) (G' := latGens.getD 7 [] ++ latGens.getD 4 []) (Z := latGens.getD 11 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c4_7r) (by quickRfl) k1c11 t11
theorem k5c7_4 : isLat7 C depth ((latGens.getD 7 [] ++ latGens.getD 4 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c7_4r z11 k1c11 t11
theorem k5c7_5r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 7 [] ++ latGens.getD 5 []).map code) depth) T11)
    (allL ((latGens.getD 7 [] ++ latGens.getD 5 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 5 [] ++ latGens.getD 7 []) (G' := latGens.getD 7 [] ++ latGens.getD 5 []) (Z := latGens.getD 11 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c5_7r) (by quickRfl) k1c11 t11
theorem k5c7_5 : isLat7 C depth ((latGens.getD 7 [] ++ latGens.getD 5 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c7_5r z11 k1c11 t11
theorem k5c7_6r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 7 [] ++ latGens.getD 6 []).map code) depth) T11)
    (allL ((latGens.getD 7 [] ++ latGens.getD 6 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 6 [] ++ latGens.getD 7 []) (G' := latGens.getD 7 [] ++ latGens.getD 6 []) (Z := latGens.getD 11 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c6_7r) (by quickRfl) k1c11 t11
theorem k5c7_6 : isLat7 C depth ((latGens.getD 7 [] ++ latGens.getD 6 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c7_6r z11 k1c11 t11
theorem k5c7_7r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 7 [] ++ latGens.getD 7 []).map code) depth) T7)
    (allL ((latGens.getD 7 [] ++ latGens.getD 7 []).map code) (memM 7 C (chainF C) T7)) = true :=
  recG_sub (G₁ := latGens.getD 7 []) (G₂ := latGens.getD 7 []) (List.Subset.refl _) t7 (by quickRfl)
theorem k5c7_7 : isLat7 C depth ((latGens.getD 7 [] ++ latGens.getD 7 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c7_7r z7 k1c7 t7
theorem k5c7_8s : setEqM (bfsM 7 C (chainF C) ((latGens.getD 7 [] ++ [perm7 [[2, 5], [3, 6]]]).map code) depth) T11 = true :=
  recG_ball (S := jS6) (m := 5) (k := 4) hok inj (by decide) jS6t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k5c7_8r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 7 [] ++ latGens.getD 8 []).map code) depth) T11)
    (allL ((latGens.getD 7 [] ++ latGens.getD 8 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_dup (G₁ := latGens.getD 7 []) (D := dGens) (N := [perm7 [[2, 5], [3, 6]]]) (List.subset_append_left _ _) k5c7_8s (by quickRfl)
theorem k5c7_8 : isLat7 C depth ((latGens.getD 7 [] ++ latGens.getD 8 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c7_8r z11 k1c11 t11
theorem k5c7_9s : setEqM (bfsM 7 C (chainF C) ((latGens.getD 7 [] ++ [perm7 [[2, 4], [3, 6]]]).map code) depth) T11 = true :=
  recG_ball (S := jS6) (m := 5) (k := 4) hok inj (by decide) jS6t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k5c7_9r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 7 [] ++ latGens.getD 9 []).map code) depth) T11)
    (allL ((latGens.getD 7 [] ++ latGens.getD 9 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_dup (G₁ := latGens.getD 7 []) (D := dGens) (N := [perm7 [[2, 4], [3, 6]]]) (List.subset_append_left _ _) k5c7_9s (by quickRfl)
theorem k5c7_9 : isLat7 C depth ((latGens.getD 7 [] ++ latGens.getD 9 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c7_9r z11 k1c11 t11
theorem k5c7_10s : setEqM (bfsM 7 C (chainF C) ((latGens.getD 7 [] ++ [perm7 [[3, 4, 5]]]).map code) depth) T11 = true :=
  recG_ball (S := jS5) (m := 5) (k := 4) hok inj (by decide) jS5t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k5c7_10r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 7 [] ++ latGens.getD 10 []).map code) depth) T11)
    (allL ((latGens.getD 7 [] ++ latGens.getD 10 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_dup (G₁ := latGens.getD 7 []) (D := dGens) (N := [perm7 [[3, 4, 5]]]) (List.subset_append_left _ _) k5c7_10s (by quickRfl)
theorem k5c7_10 : isLat7 C depth ((latGens.getD 7 [] ++ latGens.getD 10 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c7_10r z11 k1c11 t11
theorem k5c7_11r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 7 [] ++ latGens.getD 11 []).map code) depth) T11)
    (allL ((latGens.getD 7 [] ++ latGens.getD 11 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 11 []) (G' := latGens.getD 7 [] ++ latGens.getD 11 []) (Z := latGens.getD 11 []) hok inj (List.subset_append_right _ _) t11 (by quickRfl) k1c11 t11
theorem k5c7_11 : isLat7 C depth ((latGens.getD 7 [] ++ latGens.getD 11 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c7_11r z11 k1c11 t11
theorem k5c7 : allA latGens (fun G₂ => isLat7 C depth
    ((latGens.getD 7 [] ++ G₂).map code) (latGens.map (List.map code))) = true :=
  allA_of_getD latGens _ [] (fun j hj => match j, hj with
    | 0, _ => k5c7_0
    | 1, _ => k5c7_1
    | 2, _ => k5c7_2
    | 3, _ => k5c7_3
    | 4, _ => k5c7_4
    | 5, _ => k5c7_5
    | 6, _ => k5c7_6
    | 7, _ => k5c7_7
    | 8, _ => k5c7_8
    | 9, _ => k5c7_9
    | 10, _ => k5c7_10
    | 11, _ => k5c7_11
    | k + 12, h => absurd h (by
      have : latGens.length = 12 := rfl
      omega))
theorem k5c8_0r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 8 [] ++ latGens.getD 0 []).map code) depth) T8)
    (allL ((latGens.getD 8 [] ++ latGens.getD 0 []).map code) (memM 7 C (chainF C) T8)) = true :=
  recG_sub (G₁ := latGens.getD 8 []) (G₂ := latGens.getD 0 []) (List.subset_append_left _ _) t8 (by quickRfl)
theorem k5c8_0 : isLat7 C depth ((latGens.getD 8 [] ++ latGens.getD 0 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c8_0r z8 k1c8 t8
theorem k5c8_1r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 8 [] ++ latGens.getD 1 []).map code) depth) T11)
    (allL ((latGens.getD 8 [] ++ latGens.getD 1 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 1 [] ++ latGens.getD 8 []) (G' := latGens.getD 8 [] ++ latGens.getD 1 []) (Z := latGens.getD 11 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c1_8r) (by quickRfl) k1c11 t11
theorem k5c8_1 : isLat7 C depth ((latGens.getD 8 [] ++ latGens.getD 1 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c8_1r z11 k1c11 t11
theorem k5c8_2r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 8 [] ++ latGens.getD 2 []).map code) depth) T8)
    (allL ((latGens.getD 8 [] ++ latGens.getD 2 []).map code) (memM 7 C (chainF C) T8)) = true :=
  recG_monoR (G := latGens.getD 8 []) (G' := latGens.getD 8 [] ++ latGens.getD 2 []) (Z := latGens.getD 8 []) hok inj (List.subset_append_left _ _) t8 (by quickRfl) k1c8 t8
theorem k5c8_2 : isLat7 C depth ((latGens.getD 8 [] ++ latGens.getD 2 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c8_2r z8 k1c8 t8
theorem k5c8_3r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 8 [] ++ latGens.getD 3 []).map code) depth) T11)
    (allL ((latGens.getD 8 [] ++ latGens.getD 3 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 3 [] ++ latGens.getD 8 []) (G' := latGens.getD 8 [] ++ latGens.getD 3 []) (Z := latGens.getD 11 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c3_8r) (by quickRfl) k1c11 t11
theorem k5c8_3 : isLat7 C depth ((latGens.getD 8 [] ++ latGens.getD 3 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c8_3r z11 k1c11 t11
theorem k5c8_4r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 8 [] ++ latGens.getD 4 []).map code) depth) T11)
    (allL ((latGens.getD 8 [] ++ latGens.getD 4 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 4 [] ++ latGens.getD 8 []) (G' := latGens.getD 8 [] ++ latGens.getD 4 []) (Z := latGens.getD 11 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c4_8r) (by quickRfl) k1c11 t11
theorem k5c8_4 : isLat7 C depth ((latGens.getD 8 [] ++ latGens.getD 4 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c8_4r z11 k1c11 t11
theorem k5c8_5r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 8 [] ++ latGens.getD 5 []).map code) depth) T8)
    (allL ((latGens.getD 8 [] ++ latGens.getD 5 []).map code) (memM 7 C (chainF C) T8)) = true :=
  recG_monoR (G := latGens.getD 8 []) (G' := latGens.getD 8 [] ++ latGens.getD 5 []) (Z := latGens.getD 8 []) hok inj (List.subset_append_left _ _) t8 (by quickRfl) k1c8 t8
theorem k5c8_5 : isLat7 C depth ((latGens.getD 8 [] ++ latGens.getD 5 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c8_5r z8 k1c8 t8
theorem k5c8_6r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 8 [] ++ latGens.getD 6 []).map code) depth) T11)
    (allL ((latGens.getD 8 [] ++ latGens.getD 6 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 6 [] ++ latGens.getD 8 []) (G' := latGens.getD 8 [] ++ latGens.getD 6 []) (Z := latGens.getD 11 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c6_8r) (by quickRfl) k1c11 t11
theorem k5c8_6 : isLat7 C depth ((latGens.getD 8 [] ++ latGens.getD 6 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c8_6r z11 k1c11 t11
theorem k5c8_7r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 8 [] ++ latGens.getD 7 []).map code) depth) T11)
    (allL ((latGens.getD 8 [] ++ latGens.getD 7 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 7 [] ++ latGens.getD 8 []) (G' := latGens.getD 8 [] ++ latGens.getD 7 []) (Z := latGens.getD 11 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c7_8r) (by quickRfl) k1c11 t11
theorem k5c8_7 : isLat7 C depth ((latGens.getD 8 [] ++ latGens.getD 7 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c8_7r z11 k1c11 t11
theorem k5c8_8r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 8 [] ++ latGens.getD 8 []).map code) depth) T8)
    (allL ((latGens.getD 8 [] ++ latGens.getD 8 []).map code) (memM 7 C (chainF C) T8)) = true :=
  recG_sub (G₁ := latGens.getD 8 []) (G₂ := latGens.getD 8 []) (List.Subset.refl _) t8 (by quickRfl)
theorem k5c8_8 : isLat7 C depth ((latGens.getD 8 [] ++ latGens.getD 8 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c8_8r z8 k1c8 t8
theorem k5c8_9s : setEqM (bfsM 7 C (chainF C) ((latGens.getD 8 [] ++ [perm7 [[2, 4], [3, 6]]]).map code) depth) T11 = true :=
  recG_ball (S := jS6) (m := 5) (k := 4) hok inj (by decide) jS6t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k5c8_9r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 8 [] ++ latGens.getD 9 []).map code) depth) T11)
    (allL ((latGens.getD 8 [] ++ latGens.getD 9 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_dup (G₁ := latGens.getD 8 []) (D := dGens) (N := [perm7 [[2, 4], [3, 6]]]) (List.subset_append_left _ _) k5c8_9s (by quickRfl)
theorem k5c8_9 : isLat7 C depth ((latGens.getD 8 [] ++ latGens.getD 9 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c8_9r z11 k1c11 t11
theorem k5c8_10s : setEqM (bfsM 7 C (chainF C) ((latGens.getD 8 [] ++ [perm7 [[3, 4, 5]]]).map code) depth) T11 = true :=
  recG_ball (S := jS2) (m := 10) (k := 2) hok inj (by decide) jS2t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k5c8_10r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 8 [] ++ latGens.getD 10 []).map code) depth) T11)
    (allL ((latGens.getD 8 [] ++ latGens.getD 10 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_dup (G₁ := latGens.getD 8 []) (D := dGens) (N := [perm7 [[3, 4, 5]]]) (List.subset_append_left _ _) k5c8_10s (by quickRfl)
theorem k5c8_10 : isLat7 C depth ((latGens.getD 8 [] ++ latGens.getD 10 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c8_10r z11 k1c11 t11
theorem k5c8_11r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 8 [] ++ latGens.getD 11 []).map code) depth) T11)
    (allL ((latGens.getD 8 [] ++ latGens.getD 11 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 11 []) (G' := latGens.getD 8 [] ++ latGens.getD 11 []) (Z := latGens.getD 11 []) hok inj (List.subset_append_right _ _) t11 (by quickRfl) k1c11 t11
theorem k5c8_11 : isLat7 C depth ((latGens.getD 8 [] ++ latGens.getD 11 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c8_11r z11 k1c11 t11
theorem k5c8 : allA latGens (fun G₂ => isLat7 C depth
    ((latGens.getD 8 [] ++ G₂).map code) (latGens.map (List.map code))) = true :=
  allA_of_getD latGens _ [] (fun j hj => match j, hj with
    | 0, _ => k5c8_0
    | 1, _ => k5c8_1
    | 2, _ => k5c8_2
    | 3, _ => k5c8_3
    | 4, _ => k5c8_4
    | 5, _ => k5c8_5
    | 6, _ => k5c8_6
    | 7, _ => k5c8_7
    | 8, _ => k5c8_8
    | 9, _ => k5c8_9
    | 10, _ => k5c8_10
    | 11, _ => k5c8_11
    | k + 12, h => absurd h (by
      have : latGens.length = 12 := rfl
      omega))
theorem k5c9_0r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 9 [] ++ latGens.getD 0 []).map code) depth) T9)
    (allL ((latGens.getD 9 [] ++ latGens.getD 0 []).map code) (memM 7 C (chainF C) T9)) = true :=
  recG_sub (G₁ := latGens.getD 9 []) (G₂ := latGens.getD 0 []) (List.subset_append_left _ _) t9 (by quickRfl)
theorem k5c9_0 : isLat7 C depth ((latGens.getD 9 [] ++ latGens.getD 0 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c9_0r z9 k1c9 t9
theorem k5c9_1r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 9 [] ++ latGens.getD 1 []).map code) depth) T11)
    (allL ((latGens.getD 9 [] ++ latGens.getD 1 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 1 [] ++ latGens.getD 9 []) (G' := latGens.getD 9 [] ++ latGens.getD 1 []) (Z := latGens.getD 11 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c1_9r) (by quickRfl) k1c11 t11
theorem k5c9_1 : isLat7 C depth ((latGens.getD 9 [] ++ latGens.getD 1 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c9_1r z11 k1c11 t11
theorem k5c9_2r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 9 [] ++ latGens.getD 2 []).map code) depth) T11)
    (allL ((latGens.getD 9 [] ++ latGens.getD 2 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 2 [] ++ latGens.getD 9 []) (G' := latGens.getD 9 [] ++ latGens.getD 2 []) (Z := latGens.getD 11 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c2_9r) (by quickRfl) k1c11 t11
theorem k5c9_2 : isLat7 C depth ((latGens.getD 9 [] ++ latGens.getD 2 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c9_2r z11 k1c11 t11
theorem k5c9_3r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 9 [] ++ latGens.getD 3 []).map code) depth) T11)
    (allL ((latGens.getD 9 [] ++ latGens.getD 3 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 3 [] ++ latGens.getD 9 []) (G' := latGens.getD 9 [] ++ latGens.getD 3 []) (Z := latGens.getD 11 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c3_9r) (by quickRfl) k1c11 t11
theorem k5c9_3 : isLat7 C depth ((latGens.getD 9 [] ++ latGens.getD 3 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c9_3r z11 k1c11 t11
theorem k5c9_4r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 9 [] ++ latGens.getD 4 []).map code) depth) T9)
    (allL ((latGens.getD 9 [] ++ latGens.getD 4 []).map code) (memM 7 C (chainF C) T9)) = true :=
  recG_monoR (G := latGens.getD 9 []) (G' := latGens.getD 9 [] ++ latGens.getD 4 []) (Z := latGens.getD 9 []) hok inj (List.subset_append_left _ _) t9 (by quickRfl) k1c9 t9
theorem k5c9_4 : isLat7 C depth ((latGens.getD 9 [] ++ latGens.getD 4 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c9_4r z9 k1c9 t9
theorem k5c9_5r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 9 [] ++ latGens.getD 5 []).map code) depth) T9)
    (allL ((latGens.getD 9 [] ++ latGens.getD 5 []).map code) (memM 7 C (chainF C) T9)) = true :=
  recG_monoR (G := latGens.getD 9 []) (G' := latGens.getD 9 [] ++ latGens.getD 5 []) (Z := latGens.getD 9 []) hok inj (List.subset_append_left _ _) t9 (by quickRfl) k1c9 t9
theorem k5c9_5 : isLat7 C depth ((latGens.getD 9 [] ++ latGens.getD 5 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c9_5r z9 k1c9 t9
theorem k5c9_6r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 9 [] ++ latGens.getD 6 []).map code) depth) T11)
    (allL ((latGens.getD 9 [] ++ latGens.getD 6 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 6 [] ++ latGens.getD 9 []) (G' := latGens.getD 9 [] ++ latGens.getD 6 []) (Z := latGens.getD 11 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c6_9r) (by quickRfl) k1c11 t11
theorem k5c9_6 : isLat7 C depth ((latGens.getD 9 [] ++ latGens.getD 6 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c9_6r z11 k1c11 t11
theorem k5c9_7r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 9 [] ++ latGens.getD 7 []).map code) depth) T11)
    (allL ((latGens.getD 9 [] ++ latGens.getD 7 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 7 [] ++ latGens.getD 9 []) (G' := latGens.getD 9 [] ++ latGens.getD 7 []) (Z := latGens.getD 11 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c7_9r) (by quickRfl) k1c11 t11
theorem k5c9_7 : isLat7 C depth ((latGens.getD 9 [] ++ latGens.getD 7 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c9_7r z11 k1c11 t11
theorem k5c9_8r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 9 [] ++ latGens.getD 8 []).map code) depth) T11)
    (allL ((latGens.getD 9 [] ++ latGens.getD 8 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 8 [] ++ latGens.getD 9 []) (G' := latGens.getD 9 [] ++ latGens.getD 8 []) (Z := latGens.getD 11 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c8_9r) (by quickRfl) k1c11 t11
theorem k5c9_8 : isLat7 C depth ((latGens.getD 9 [] ++ latGens.getD 8 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c9_8r z11 k1c11 t11
theorem k5c9_9r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 9 [] ++ latGens.getD 9 []).map code) depth) T9)
    (allL ((latGens.getD 9 [] ++ latGens.getD 9 []).map code) (memM 7 C (chainF C) T9)) = true :=
  recG_sub (G₁ := latGens.getD 9 []) (G₂ := latGens.getD 9 []) (List.Subset.refl _) t9 (by quickRfl)
theorem k5c9_9 : isLat7 C depth ((latGens.getD 9 [] ++ latGens.getD 9 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c9_9r z9 k1c9 t9
theorem k5c9_10s : setEqM (bfsM 7 C (chainF C) ((latGens.getD 9 [] ++ [perm7 [[3, 4, 5]]]).map code) depth) T11 = true :=
  recG_ball (S := jS6) (m := 5) (k := 4) hok inj (by decide) jS6t (by quickRfl) (by quickRfl) (by quickRfl) k1c11 t11
theorem k5c9_10r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 9 [] ++ latGens.getD 10 []).map code) depth) T11)
    (allL ((latGens.getD 9 [] ++ latGens.getD 10 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_dup (G₁ := latGens.getD 9 []) (D := dGens) (N := [perm7 [[3, 4, 5]]]) (List.subset_append_left _ _) k5c9_10s (by quickRfl)
theorem k5c9_10 : isLat7 C depth ((latGens.getD 9 [] ++ latGens.getD 10 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c9_10r z11 k1c11 t11
theorem k5c9_11r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 9 [] ++ latGens.getD 11 []).map code) depth) T11)
    (allL ((latGens.getD 9 [] ++ latGens.getD 11 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 11 []) (G' := latGens.getD 9 [] ++ latGens.getD 11 []) (Z := latGens.getD 11 []) hok inj (List.subset_append_right _ _) t11 (by quickRfl) k1c11 t11
theorem k5c9_11 : isLat7 C depth ((latGens.getD 9 [] ++ latGens.getD 11 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c9_11r z11 k1c11 t11
theorem k5c9 : allA latGens (fun G₂ => isLat7 C depth
    ((latGens.getD 9 [] ++ G₂).map code) (latGens.map (List.map code))) = true :=
  allA_of_getD latGens _ [] (fun j hj => match j, hj with
    | 0, _ => k5c9_0
    | 1, _ => k5c9_1
    | 2, _ => k5c9_2
    | 3, _ => k5c9_3
    | 4, _ => k5c9_4
    | 5, _ => k5c9_5
    | 6, _ => k5c9_6
    | 7, _ => k5c9_7
    | 8, _ => k5c9_8
    | 9, _ => k5c9_9
    | 10, _ => k5c9_10
    | 11, _ => k5c9_11
    | k + 12, h => absurd h (by
      have : latGens.length = 12 := rfl
      omega))
theorem k5c10_0r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 10 [] ++ latGens.getD 0 []).map code) depth) T10)
    (allL ((latGens.getD 10 [] ++ latGens.getD 0 []).map code) (memM 7 C (chainF C) T10)) = true :=
  recG_sub (G₁ := latGens.getD 10 []) (G₂ := latGens.getD 0 []) (List.subset_append_left _ _) t10 (by quickRfl)
theorem k5c10_0 : isLat7 C depth ((latGens.getD 10 [] ++ latGens.getD 0 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c10_0r z10 k1c10 t10
theorem k5c10_1r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 10 [] ++ latGens.getD 1 []).map code) depth) T11)
    (allL ((latGens.getD 10 [] ++ latGens.getD 1 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 1 [] ++ latGens.getD 10 []) (G' := latGens.getD 10 [] ++ latGens.getD 1 []) (Z := latGens.getD 11 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c1_10r) (by quickRfl) k1c11 t11
theorem k5c10_1 : isLat7 C depth ((latGens.getD 10 [] ++ latGens.getD 1 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c10_1r z11 k1c11 t11
theorem k5c10_2r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 10 [] ++ latGens.getD 2 []).map code) depth) T11)
    (allL ((latGens.getD 10 [] ++ latGens.getD 2 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 2 [] ++ latGens.getD 10 []) (G' := latGens.getD 10 [] ++ latGens.getD 2 []) (Z := latGens.getD 11 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c2_10r) (by quickRfl) k1c11 t11
theorem k5c10_2 : isLat7 C depth ((latGens.getD 10 [] ++ latGens.getD 2 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c10_2r z11 k1c11 t11
theorem k5c10_3r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 10 [] ++ latGens.getD 3 []).map code) depth) T10)
    (allL ((latGens.getD 10 [] ++ latGens.getD 3 []).map code) (memM 7 C (chainF C) T10)) = true :=
  recG_monoR (G := latGens.getD 10 []) (G' := latGens.getD 10 [] ++ latGens.getD 3 []) (Z := latGens.getD 10 []) hok inj (List.subset_append_left _ _) t10 (by quickRfl) k1c10 t10
theorem k5c10_3 : isLat7 C depth ((latGens.getD 10 [] ++ latGens.getD 3 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c10_3r z10 k1c10 t10
theorem k5c10_4r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 10 [] ++ latGens.getD 4 []).map code) depth) T11)
    (allL ((latGens.getD 10 [] ++ latGens.getD 4 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 4 [] ++ latGens.getD 10 []) (G' := latGens.getD 10 [] ++ latGens.getD 4 []) (Z := latGens.getD 11 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c4_10r) (by quickRfl) k1c11 t11
theorem k5c10_4 : isLat7 C depth ((latGens.getD 10 [] ++ latGens.getD 4 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c10_4r z11 k1c11 t11
theorem k5c10_5r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 10 [] ++ latGens.getD 5 []).map code) depth) T10)
    (allL ((latGens.getD 10 [] ++ latGens.getD 5 []).map code) (memM 7 C (chainF C) T10)) = true :=
  recG_monoR (G := latGens.getD 10 []) (G' := latGens.getD 10 [] ++ latGens.getD 5 []) (Z := latGens.getD 10 []) hok inj (List.subset_append_left _ _) t10 (by quickRfl) k1c10 t10
theorem k5c10_5 : isLat7 C depth ((latGens.getD 10 [] ++ latGens.getD 5 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c10_5r z10 k1c10 t10
theorem k5c10_6r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 10 [] ++ latGens.getD 6 []).map code) depth) T11)
    (allL ((latGens.getD 10 [] ++ latGens.getD 6 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 6 [] ++ latGens.getD 10 []) (G' := latGens.getD 10 [] ++ latGens.getD 6 []) (Z := latGens.getD 11 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c6_10r) (by quickRfl) k1c11 t11
theorem k5c10_6 : isLat7 C depth ((latGens.getD 10 [] ++ latGens.getD 6 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c10_6r z11 k1c11 t11
theorem k5c10_7r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 10 [] ++ latGens.getD 7 []).map code) depth) T11)
    (allL ((latGens.getD 10 [] ++ latGens.getD 7 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 7 [] ++ latGens.getD 10 []) (G' := latGens.getD 10 [] ++ latGens.getD 7 []) (Z := latGens.getD 11 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c7_10r) (by quickRfl) k1c11 t11
theorem k5c10_7 : isLat7 C depth ((latGens.getD 10 [] ++ latGens.getD 7 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c10_7r z11 k1c11 t11
theorem k5c10_8r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 10 [] ++ latGens.getD 8 []).map code) depth) T11)
    (allL ((latGens.getD 10 [] ++ latGens.getD 8 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 8 [] ++ latGens.getD 10 []) (G' := latGens.getD 10 [] ++ latGens.getD 8 []) (Z := latGens.getD 11 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c8_10r) (by quickRfl) k1c11 t11
theorem k5c10_8 : isLat7 C depth ((latGens.getD 10 [] ++ latGens.getD 8 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c10_8r z11 k1c11 t11
theorem k5c10_9r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 10 [] ++ latGens.getD 9 []).map code) depth) T11)
    (allL ((latGens.getD 10 [] ++ latGens.getD 9 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 9 [] ++ latGens.getD 10 []) (G' := latGens.getD 10 [] ++ latGens.getD 9 []) (Z := latGens.getD 11 []) hok inj (fun _ hx => List.mem_append.2 (List.mem_append.1 hx).symm) (setEqM_of_recR k5c9_10r) (by quickRfl) k1c11 t11
theorem k5c10_9 : isLat7 C depth ((latGens.getD 10 [] ++ latGens.getD 9 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c10_9r z11 k1c11 t11
theorem k5c10_10r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 10 [] ++ latGens.getD 10 []).map code) depth) T10)
    (allL ((latGens.getD 10 [] ++ latGens.getD 10 []).map code) (memM 7 C (chainF C) T10)) = true :=
  recG_sub (G₁ := latGens.getD 10 []) (G₂ := latGens.getD 10 []) (List.Subset.refl _) t10 (by quickRfl)
theorem k5c10_10 : isLat7 C depth ((latGens.getD 10 [] ++ latGens.getD 10 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c10_10r z10 k1c10 t10
theorem k5c10_11r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 10 [] ++ latGens.getD 11 []).map code) depth) T11)
    (allL ((latGens.getD 10 [] ++ latGens.getD 11 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 11 []) (G' := latGens.getD 10 [] ++ latGens.getD 11 []) (Z := latGens.getD 11 []) hok inj (List.subset_append_right _ _) t11 (by quickRfl) k1c11 t11
theorem k5c10_11 : isLat7 C depth ((latGens.getD 10 [] ++ latGens.getD 11 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c10_11r z11 k1c11 t11
theorem k5c10 : allA latGens (fun G₂ => isLat7 C depth
    ((latGens.getD 10 [] ++ G₂).map code) (latGens.map (List.map code))) = true :=
  allA_of_getD latGens _ [] (fun j hj => match j, hj with
    | 0, _ => k5c10_0
    | 1, _ => k5c10_1
    | 2, _ => k5c10_2
    | 3, _ => k5c10_3
    | 4, _ => k5c10_4
    | 5, _ => k5c10_5
    | 6, _ => k5c10_6
    | 7, _ => k5c10_7
    | 8, _ => k5c10_8
    | 9, _ => k5c10_9
    | 10, _ => k5c10_10
    | 11, _ => k5c10_11
    | k + 12, h => absurd h (by
      have : latGens.length = 12 := rfl
      omega))
theorem k5c11_0r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 11 [] ++ latGens.getD 0 []).map code) depth) T11)
    (allL ((latGens.getD 11 [] ++ latGens.getD 0 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_sub (G₁ := latGens.getD 11 []) (G₂ := latGens.getD 0 []) (List.subset_append_left _ _) t11 (by quickRfl)
theorem k5c11_0 : isLat7 C depth ((latGens.getD 11 [] ++ latGens.getD 0 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c11_0r z11 k1c11 t11
theorem k5c11_1r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 11 [] ++ latGens.getD 1 []).map code) depth) T11)
    (allL ((latGens.getD 11 [] ++ latGens.getD 1 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 11 []) (G' := latGens.getD 11 [] ++ latGens.getD 1 []) (Z := latGens.getD 11 []) hok inj (List.subset_append_left _ _) t11 (by quickRfl) k1c11 t11
theorem k5c11_1 : isLat7 C depth ((latGens.getD 11 [] ++ latGens.getD 1 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c11_1r z11 k1c11 t11
theorem k5c11_2r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 11 [] ++ latGens.getD 2 []).map code) depth) T11)
    (allL ((latGens.getD 11 [] ++ latGens.getD 2 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 11 []) (G' := latGens.getD 11 [] ++ latGens.getD 2 []) (Z := latGens.getD 11 []) hok inj (List.subset_append_left _ _) t11 (by quickRfl) k1c11 t11
theorem k5c11_2 : isLat7 C depth ((latGens.getD 11 [] ++ latGens.getD 2 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c11_2r z11 k1c11 t11
theorem k5c11_3r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 11 [] ++ latGens.getD 3 []).map code) depth) T11)
    (allL ((latGens.getD 11 [] ++ latGens.getD 3 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 11 []) (G' := latGens.getD 11 [] ++ latGens.getD 3 []) (Z := latGens.getD 11 []) hok inj (List.subset_append_left _ _) t11 (by quickRfl) k1c11 t11
theorem k5c11_3 : isLat7 C depth ((latGens.getD 11 [] ++ latGens.getD 3 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c11_3r z11 k1c11 t11
theorem k5c11_4r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 11 [] ++ latGens.getD 4 []).map code) depth) T11)
    (allL ((latGens.getD 11 [] ++ latGens.getD 4 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 11 []) (G' := latGens.getD 11 [] ++ latGens.getD 4 []) (Z := latGens.getD 11 []) hok inj (List.subset_append_left _ _) t11 (by quickRfl) k1c11 t11
theorem k5c11_4 : isLat7 C depth ((latGens.getD 11 [] ++ latGens.getD 4 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c11_4r z11 k1c11 t11
theorem k5c11_5r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 11 [] ++ latGens.getD 5 []).map code) depth) T11)
    (allL ((latGens.getD 11 [] ++ latGens.getD 5 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 11 []) (G' := latGens.getD 11 [] ++ latGens.getD 5 []) (Z := latGens.getD 11 []) hok inj (List.subset_append_left _ _) t11 (by quickRfl) k1c11 t11
theorem k5c11_5 : isLat7 C depth ((latGens.getD 11 [] ++ latGens.getD 5 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c11_5r z11 k1c11 t11
theorem k5c11_6r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 11 [] ++ latGens.getD 6 []).map code) depth) T11)
    (allL ((latGens.getD 11 [] ++ latGens.getD 6 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 11 []) (G' := latGens.getD 11 [] ++ latGens.getD 6 []) (Z := latGens.getD 11 []) hok inj (List.subset_append_left _ _) t11 (by quickRfl) k1c11 t11
theorem k5c11_6 : isLat7 C depth ((latGens.getD 11 [] ++ latGens.getD 6 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c11_6r z11 k1c11 t11
theorem k5c11_7r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 11 [] ++ latGens.getD 7 []).map code) depth) T11)
    (allL ((latGens.getD 11 [] ++ latGens.getD 7 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 11 []) (G' := latGens.getD 11 [] ++ latGens.getD 7 []) (Z := latGens.getD 11 []) hok inj (List.subset_append_left _ _) t11 (by quickRfl) k1c11 t11
theorem k5c11_7 : isLat7 C depth ((latGens.getD 11 [] ++ latGens.getD 7 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c11_7r z11 k1c11 t11
theorem k5c11_8r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 11 [] ++ latGens.getD 8 []).map code) depth) T11)
    (allL ((latGens.getD 11 [] ++ latGens.getD 8 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 11 []) (G' := latGens.getD 11 [] ++ latGens.getD 8 []) (Z := latGens.getD 11 []) hok inj (List.subset_append_left _ _) t11 (by quickRfl) k1c11 t11
theorem k5c11_8 : isLat7 C depth ((latGens.getD 11 [] ++ latGens.getD 8 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c11_8r z11 k1c11 t11
theorem k5c11_9r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 11 [] ++ latGens.getD 9 []).map code) depth) T11)
    (allL ((latGens.getD 11 [] ++ latGens.getD 9 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 11 []) (G' := latGens.getD 11 [] ++ latGens.getD 9 []) (Z := latGens.getD 11 []) hok inj (List.subset_append_left _ _) t11 (by quickRfl) k1c11 t11
theorem k5c11_9 : isLat7 C depth ((latGens.getD 11 [] ++ latGens.getD 9 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c11_9r z11 k1c11 t11
theorem k5c11_10r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 11 [] ++ latGens.getD 10 []).map code) depth) T11)
    (allL ((latGens.getD 11 [] ++ latGens.getD 10 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_monoR (G := latGens.getD 11 []) (G' := latGens.getD 11 [] ++ latGens.getD 10 []) (Z := latGens.getD 11 []) hok inj (List.subset_append_left _ _) t11 (by quickRfl) k1c11 t11
theorem k5c11_10 : isLat7 C depth ((latGens.getD 11 [] ++ latGens.getD 10 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c11_10r z11 k1c11 t11
theorem k5c11_11r : CFSG.KC.Ord.andB (setEqM (bfsM 7 C (chainF C) ((latGens.getD 11 [] ++ latGens.getD 11 []).map code) depth) T11)
    (allL ((latGens.getD 11 [] ++ latGens.getD 11 []).map code) (memM 7 C (chainF C) T11)) = true :=
  recG_sub (G₁ := latGens.getD 11 []) (G₂ := latGens.getD 11 []) (List.Subset.refl _) t11 (by quickRfl)
theorem k5c11_11 : isLat7 C depth ((latGens.getD 11 [] ++ latGens.getD 11 []).map code) (latGens.map (List.map code)) = true :=
  isLat7_of_recG hok inj k5c11_11r z11 k1c11 t11
theorem k5c11 : allA latGens (fun G₂ => isLat7 C depth
    ((latGens.getD 11 [] ++ G₂).map code) (latGens.map (List.map code))) = true :=
  allA_of_getD latGens _ [] (fun j hj => match j, hj with
    | 0, _ => k5c11_0
    | 1, _ => k5c11_1
    | 2, _ => k5c11_2
    | 3, _ => k5c11_3
    | 4, _ => k5c11_4
    | 5, _ => k5c11_5
    | 6, _ => k5c11_6
    | 7, _ => k5c11_7
    | 8, _ => k5c11_8
    | 9, _ => k5c11_9
    | 10, _ => k5c11_10
    | 11, _ => k5c11_11
    | k + 12, h => absurd h (by
      have : latGens.length = 12 := rfl
      omega))
theorem k5 : allA latGens (fun G₁ => allA latGens fun G₂ =>
    isLat7 C depth ((G₁ ++ G₂).map code) (latGens.map (List.map code))) = true :=
  allA_of_getD latGens _ [] (fun i hi => match i, hi with
    | 0, _ => k5c0
    | 1, _ => k5c1
    | 2, _ => k5c2
    | 3, _ => k5c3
    | 4, _ => k5c4
    | 5, _ => k5c5
    | 6, _ => k5c6
    | 7, _ => k5c7
    | 8, _ => k5c8
    | 9, _ => k5c9
    | 10, _ => k5c10
    | 11, _ => k5c11
    | k + 12, h => absurd h (by
      have : latGens.length = 12 := rfl
      omega))

end CFSG.KD.LQT.C4058

end
