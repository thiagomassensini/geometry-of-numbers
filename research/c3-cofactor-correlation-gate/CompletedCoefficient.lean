import BaseCoefficient

namespace C3CofactorCorrelation

open CarryC3Boxes CarryC3Tail CarryC3Gamma C3Cofactor
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000

def normalizedOuterCompletedPolynomialCoefficient
    (q ell : ℝ) (n e : ℕ) : ℝ :=
  if e ≤ n then
    ∑ j ∈ Finset.range (n + 1),
      if e ≤ j then
        normalizedOuterBasePolynomialCoeff q ell j e * normalizedGammaJet (n - j)
      else 0
  else 0

def normalizedOuterCompletedPolynomialHorner
    (p q ell : ℝ) (n : ℕ) : ℝ :=
  ∑ e ∈ Finset.range (n + 1),
    normalizedOuterCompletedPolynomialCoefficient q ell n e * p ^ e

theorem normalized_outer_completed_jet_eq_polynomial (r : Fin 13) :
    normalizedOuterCompletedJet48 r.val =
      normalizedOuterCompletedPolynomialHorner (Real.log Real.pi)
        chartRatio (Real.log 3) r.val := by
  have hbase (g : ℕ) (hg : g ∈ Finset.range (r.val + 1)) :
      normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3)
          g =
        normalizedOuterBaseHorner (Real.log Real.pi) chartRatio (Real.log 3)
          g := by
    have hlt : g < 13 := by
      have hle := Finset.mem_range.mp hg
      have hr := r.isLt
      omega
    exact normalizedOuterBaseJet_eq_horner ⟨g, hlt⟩
      (Real.log Real.pi) chartRatio (Real.log 3)
  unfold normalizedOuterCompletedJet48 convolution
  rw [show (∑ g ∈ Finset.range (r.val + 1),
      normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) g *
        normalizedGammaJet (r.val - g)) =
      ∑ g ∈ Finset.range (r.val + 1),
        normalizedOuterBaseHorner (Real.log Real.pi) chartRatio (Real.log 3)
          g * normalizedGammaJet (r.val - g) by
        apply Finset.sum_congr rfl
        intro g hg
        rw [hbase g hg]]
  fin_cases r <;>
    simp [normalizedOuterBaseHorner, normalizedOuterCompletedPolynomialHorner,
      normalizedOuterCompletedPolynomialCoefficient, normalizedGammaJet,
      Finset.sum_range_succ] <;> ring

def normalizedGammaCoefficientQ (g : ℕ) : ℚ :=
  if hg : g < 13 then
    gammaRealReference13 ⟨g, hg⟩ /
      gammaRealReference13 ⟨0, by omega⟩
  else 0

theorem normalized_gamma_coefficient_point (g : ℕ) :
    (Box.point (normalizedGammaCoefficientQ g)).Contains (normalizedGammaJet g) := by
  by_cases hg : g < 13
  · simp [normalizedGammaCoefficientQ, normalizedGammaJet, hg,
      Box.point, Box.Contains]
  · simp [normalizedGammaCoefficientQ, normalizedGammaJet, hg,
      Box.point, Box.Contains]

def normalizedOuterCompletedPolynomialCoefficientBoxTable : Fin 13 → Fin 13 → Box := ![
  ![
    ⟨1 / 1, 500000000000000000000001 / 500000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩
  ],
  ![
    ⟨485617817210377798827681 / 1000000000000000000000000, 97123563442075559765537 / 200000000000000000000000⟩,
    ⟨-1 / 2, -249999999999999999999999 / 500000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩
  ],
  ![
    ⟨109019329126918101045621 / 500000000000000000000000, 174430926603068961673 / 800000000000000000000⟩,
    ⟨-48561781721037779882769 / 200000000000000000000000, -242808908605188899413841 / 1000000000000000000000000⟩,
    ⟨1 / 8, 62500000000000000000001 / 500000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩
  ],
  ![
    ⟨78121774556799279743 / 2000000000000000000000, 39060887278399639871517 / 1000000000000000000000000⟩,
    ⟨-174430926603068961673 / 1600000000000000000000, -6813708070432381315351 / 62500000000000000000000⟩,
    ⟨30351113575648612426729 / 500000000000000000000000, 30351113575648612426731 / 500000000000000000000000⟩,
    ⟨-10416666666666666666667 / 500000000000000000000000, -5208333333333333333333 / 250000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩
  ],
  ![
    ⟨3234773447772972753357 / 250000000000000000000000, 6469546895545945506731 / 500000000000000000000000⟩,
    ⟨-2441305454899977491971 / 125000000000000000000000, -78121774556799279743 / 4000000000000000000000⟩,
    ⟨27254832281729525261403 / 1000000000000000000000000, 27254832281729525261411 / 1000000000000000000000000⟩,
    ⟨-10117037858549537475579 / 1000000000000000000000000, -404681514341981499023 / 40000000000000000000000⟩,
    ⟨1302083333333333333333 / 500000000000000000000000, 651041666666666666667 / 250000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩
  ],
  ![
    ⟨-41455978657154937307 / 500000000000000000000000, -5181997332144367159 / 62500000000000000000000⟩,
    ⟨-646954689554594550673 / 100000000000000000000000, -1293909379109189101339 / 200000000000000000000000⟩,
    ⟨4882610909799954983927 / 1000000000000000000000000, 610326363724994372993 / 125000000000000000000000⟩,
    ⟨-908494409390984175381 / 200000000000000000000000, -4542472046954920876897 / 1000000000000000000000000⟩,
    ⟨632314866159346092223 / 500000000000000000000000, 25292594646373843689 / 20000000000000000000000⟩,
    ⟨-260416666666666666667 / 1000000000000000000000000, -52083333333333333333 / 200000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩
  ],
  ![
    ⟨813022121110174358919 / 1000000000000000000000000, 40651106055508717953 / 50000000000000000000000⟩,
    ⟨8291195731430987447 / 200000000000000000000000, 8291195731430987461 / 200000000000000000000000⟩,
    ⟨161738672388648637667 / 100000000000000000000000, 323477344777297275341 / 200000000000000000000000⟩,
    ⟨-406884242483329581999 / 500000000000000000000000, -813768484966659163981 / 1000000000000000000000000⟩,
    ⟨567809005869365109607 / 1000000000000000000000000, 113561801173873021923 / 200000000000000000000000⟩,
    ⟨-126462973231869218447 / 1000000000000000000000000, -126462973231869218443 / 1000000000000000000000000⟩,
    ⟨2712673611111111111 / 125000000000000000000000, 2170138888888888889 / 100000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩
  ],
  ![
    ⟨-54192378639777421687 / 250000000000000000000000, -108384757279554843233 / 500000000000000000000000⟩,
    ⟨-203255530277543589763 / 500000000000000000000000, -81302212111017435877 / 200000000000000000000000⟩,
    ⟨-10363994664288734371 / 1000000000000000000000000, -10363994664288734301 / 1000000000000000000000000⟩,
    ⟨-269564453981081062797 / 1000000000000000000000000, -134782226990540531381 / 500000000000000000000000⟩,
    ⟨50860530310416197747 / 500000000000000000000000, 101721060620832395511 / 1000000000000000000000000⟩,
    ⟨-11356180117387302193 / 200000000000000000000000, -56780900586936510957 / 1000000000000000000000000⟩,
    ⟨5269290551327884101 / 500000000000000000000000, 5269290551327884103 / 500000000000000000000000⟩,
    ⟨-31001984126984127 / 20000000000000000000000, -387524801587301587 / 250000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩
  ],
  ![
    ⟨100769662900186553899 / 1000000000000000000000000, 100769662900186554463 / 1000000000000000000000000⟩,
    ⟨27096189319888710771 / 250000000000000000000000, 54192378639777421683 / 500000000000000000000000⟩,
    ⟨10162776513877179483 / 100000000000000000000000, 101627765138771794971 / 1000000000000000000000000⟩,
    ⟨107958277753007647 / 62500000000000000000000, 863666222024061211 / 500000000000000000000000⟩,
    ⟨33695556747635132823 / 1000000000000000000000000, 16847778373817566429 / 500000000000000000000000⟩,
    ⟨-10172106062083239559 / 1000000000000000000000000, -5086053031041619771 / 500000000000000000000000⟩,
    ⟨189269668623121703 / 40000000000000000000000, 591467714447255323 / 125000000000000000000000⟩,
    ⟨-752755793046840587 / 1000000000000000000000000, -752755793046840583 / 1000000000000000000000000⟩,
    ⟨24220300099206349 / 250000000000000000000000, 48440600198412699 / 500000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩
  ],
  ![
    ⟨-19387647916454377721 / 500000000000000000000000, -38775295832908754313 / 1000000000000000000000000⟩,
    ⟨-50384831450093277217 / 1000000000000000000000000, -12596207862523319163 / 250000000000000000000000⟩,
    ⟨-27096189319888711021 / 1000000000000000000000000, -27096189319888710739 / 1000000000000000000000000⟩,
    ⟨-8468980428230982941 / 500000000000000000000000, -16937960856461965741 / 1000000000000000000000000⟩,
    ⟨-107958277753007659 / 500000000000000000000000, -13494784719125953 / 62500000000000000000000⟩,
    ⟨-1684777837381756651 / 500000000000000000000000, -3369555674763513267 / 1000000000000000000000000⟩,
    ⟨847675505173603289 / 1000000000000000000000000, 423837752586801653 / 500000000000000000000000⟩,
    ⟨-84495387778179333 / 250000000000000000000000, -84495387778179331 / 250000000000000000000000⟩,
    ⟨9409447413085507 / 200000000000000000000000, 47047237065427539 / 1000000000000000000000000⟩,
    ⟨-1076457782186949 / 200000000000000000000000, -5382288910934743 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩
  ],
  ![
    ⟨15655887036140673883 / 1000000000000000000000000, 15655887036140676143 / 1000000000000000000000000⟩,
    ⟨9693823958227188281 / 500000000000000000000000, 4846911979113594423 / 250000000000000000000000⟩,
    ⟨6298103931261659549 / 500000000000000000000000, 12596207862523319663 / 1000000000000000000000000⟩,
    ⟨903206310662956999 / 200000000000000000000000, 4516031553314785277 / 1000000000000000000000000⟩,
    ⟨3387592171292393 / 1600000000000000000000, 1058622553528872883 / 500000000000000000000000⟩,
    ⟨10795827775300747 / 500000000000000000000000, 5397913887650391 / 250000000000000000000000⟩,
    ⟨17549769139393297 / 62500000000000000000000, 280796306230292787 / 1000000000000000000000000⟩,
    ⟨-60548250369543099 / 1000000000000000000000000, -30274125184771541 / 500000000000000000000000⟩,
    ⟨21123846944544827 / 1000000000000000000000000, 5280961736136209 / 250000000000000000000000⟩,
    ⟨-1306867696261877 / 500000000000000000000000, -2090988314019 / 800000000000000000000⟩,
    ⟨269114445546737 / 1000000000000000000000000, 269114445546739 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩
  ],
  ![
    ⟨-1249914570089787571 / 200000000000000000000000, -6249572850448933331 / 1000000000000000000000000⟩,
    ⟨-3913971759035169007 / 500000000000000000000000, -3913971759035167877 / 500000000000000000000000⟩,
    ⟨-242345598955679757 / 50000000000000000000000, -4846911979113594011 / 1000000000000000000000000⟩,
    ⟨-1049683988543610079 / 500000000000000000000000, -2099367977087219593 / 1000000000000000000000000⟩,
    ⟨-564503944164348221 / 1000000000000000000000000, -564503944164347939 / 1000000000000000000000000⟩,
    ⟨-211724510705774641 / 1000000000000000000000000, -423449021411549 / 2000000000000000000000⟩,
    ⟨-899652314608411 / 500000000000000000000000, -1799304629216751 / 1000000000000000000000000⟩,
    ⟨-10028439508224753 / 500000000000000000000000, -20056879016449471 / 1000000000000000000000000⟩,
    ⟨3784265648096437 / 1000000000000000000000000, 1892132824048227 / 500000000000000000000000⟩,
    ⟨-1173547052474717 / 1000000000000000000000000, -1173547052474709 / 1000000000000000000000000⟩,
    ⟨26137353925237 / 200000000000000000000000, 13068676962619 / 100000000000000000000000⟩,
    ⟨-12232474797579 / 1000000000000000000000000, -12232474797577 / 1000000000000000000000000⟩,
    ⟨0 / 1, 1 / 1000000000000000000000000⟩
  ],
  ![
    ⟨2501730717998371353 / 1000000000000000000000000, 625432679499595103 / 250000000000000000000000⟩,
    ⟨3124786425224464289 / 1000000000000000000000000, 781196606306117203 / 250000000000000000000000⟩,
    ⟨1956985879517583679 / 1000000000000000000000000, 978492939758792969 / 500000000000000000000000⟩,
    ⟨807818663185598489 / 1000000000000000000000000, 403909331592799809 / 500000000000000000000000⟩,
    ⟨262420997135902079 / 1000000000000000000000000, 262420997135902643 / 1000000000000000000000000⟩,
    ⟨5645039441643467 / 100000000000000000000000, 7056299302054369 / 125000000000000000000000⟩,
    ⟨17643709225481129 / 1000000000000000000000000, 1764370922548127 / 100000000000000000000000⟩,
    ⟨8032609951859 / 62500000000000000000000, 25704351845963 / 200000000000000000000000⟩,
    ⟨1253554938528071 / 1000000000000000000000000, 626777469264053 / 500000000000000000000000⟩,
    ⟨-210236980449811 / 1000000000000000000000000, -105118490224897 / 500000000000000000000000⟩,
    ⟨58677352623731 / 1000000000000000000000000, 2933867631187 / 50000000000000000000000⟩,
    ⟨-1485076927571 / 250000000000000000000000, -148507692757 / 25000000000000000000000⟩,
    ⟨509686449899 / 1000000000000000000000000, 509686449901 / 1000000000000000000000000⟩
  ]
]

def normalizedOuterCompletedPolynomialCoefficientBoxCalc
    (n e : ℕ) : Box :=
  if e ≤ n then
    exactRangeSumBox (fun g =>
      if e ≤ g then
        (normalizedOuterBasePolynomialCoefficientBox g e).mul
          (Box.point (normalizedGammaCoefficientQ (n - g)))
      else Box.point 0) n
  else Box.point 0

def normalizedOuterCompletedPolynomialCoefficientBox (n e : ℕ) : Box :=
  if hn : n < 13 then
    if he : e < 13 then
      normalizedOuterCompletedPolynomialCoefficientBoxTable ⟨n, hn⟩ ⟨e, he⟩
    else normalizedOuterCompletedPolynomialCoefficientBoxCalc n e
  else normalizedOuterCompletedPolynomialCoefficientBoxCalc n e

theorem normalized_outer_completed_polynomial_coefficient_box_row_0 (e : Fin 13) :
    (normalizedOuterCompletedPolynomialCoefficientBoxCalc 0 e.val).Subset
      (normalizedOuterCompletedPolynomialCoefficientBoxTable 0 e) := by
  fin_cases e <;> decide +kernel

theorem normalized_outer_completed_polynomial_coefficient_box_row_1 (e : Fin 13) :
    (normalizedOuterCompletedPolynomialCoefficientBoxCalc 1 e.val).Subset
      (normalizedOuterCompletedPolynomialCoefficientBoxTable 1 e) := by
  fin_cases e <;> decide +kernel

theorem normalized_outer_completed_polynomial_coefficient_box_row_2 (e : Fin 13) :
    (normalizedOuterCompletedPolynomialCoefficientBoxCalc 2 e.val).Subset
      (normalizedOuterCompletedPolynomialCoefficientBoxTable 2 e) := by
  fin_cases e <;> decide +kernel

theorem normalized_outer_completed_polynomial_coefficient_box_row_3 (e : Fin 13) :
    (normalizedOuterCompletedPolynomialCoefficientBoxCalc 3 e.val).Subset
      (normalizedOuterCompletedPolynomialCoefficientBoxTable 3 e) := by
  fin_cases e <;> decide +kernel

theorem normalized_outer_completed_polynomial_coefficient_box_row_4 (e : Fin 13) :
    (normalizedOuterCompletedPolynomialCoefficientBoxCalc 4 e.val).Subset
      (normalizedOuterCompletedPolynomialCoefficientBoxTable 4 e) := by
  fin_cases e <;> decide +kernel

theorem normalized_outer_completed_polynomial_coefficient_box_row_5 (e : Fin 13) :
    (normalizedOuterCompletedPolynomialCoefficientBoxCalc 5 e.val).Subset
      (normalizedOuterCompletedPolynomialCoefficientBoxTable 5 e) := by
  fin_cases e <;> decide +kernel

theorem normalized_outer_completed_polynomial_coefficient_box_row_6 (e : Fin 13) :
    (normalizedOuterCompletedPolynomialCoefficientBoxCalc 6 e.val).Subset
      (normalizedOuterCompletedPolynomialCoefficientBoxTable 6 e) := by
  fin_cases e <;> decide +kernel

theorem normalized_outer_completed_polynomial_coefficient_box_row_7 (e : Fin 13) :
    (normalizedOuterCompletedPolynomialCoefficientBoxCalc 7 e.val).Subset
      (normalizedOuterCompletedPolynomialCoefficientBoxTable 7 e) := by
  fin_cases e <;> decide +kernel

theorem normalized_outer_completed_polynomial_coefficient_box_row_8 (e : Fin 13) :
    (normalizedOuterCompletedPolynomialCoefficientBoxCalc 8 e.val).Subset
      (normalizedOuterCompletedPolynomialCoefficientBoxTable 8 e) := by
  fin_cases e <;> decide +kernel

theorem normalized_outer_completed_polynomial_coefficient_box_row_9 (e : Fin 13) :
    (normalizedOuterCompletedPolynomialCoefficientBoxCalc 9 e.val).Subset
      (normalizedOuterCompletedPolynomialCoefficientBoxTable 9 e) := by
  fin_cases e <;> decide +kernel

theorem normalized_outer_completed_polynomial_coefficient_box_row_10 (e : Fin 13) :
    (normalizedOuterCompletedPolynomialCoefficientBoxCalc 10 e.val).Subset
      (normalizedOuterCompletedPolynomialCoefficientBoxTable 10 e) := by
  fin_cases e <;> decide +kernel

theorem normalized_outer_completed_polynomial_coefficient_box_row_11 (e : Fin 13) :
    (normalizedOuterCompletedPolynomialCoefficientBoxCalc 11 e.val).Subset
      (normalizedOuterCompletedPolynomialCoefficientBoxTable 11 e) := by
  fin_cases e <;> decide +kernel

theorem normalized_outer_completed_polynomial_coefficient_box_row_12 (e : Fin 13) :
    (normalizedOuterCompletedPolynomialCoefficientBoxCalc 12 e.val).Subset
      (normalizedOuterCompletedPolynomialCoefficientBoxTable 12 e) := by
  fin_cases e <;> decide +kernel

theorem normalized_outer_completed_polynomial_coefficient_box_table_bound
    (n e : Fin 13) :
    (normalizedOuterCompletedPolynomialCoefficientBoxCalc n.val e.val).Subset
      (normalizedOuterCompletedPolynomialCoefficientBoxTable n e) := by
  fin_cases n
  · exact normalized_outer_completed_polynomial_coefficient_box_row_0 e
  · exact normalized_outer_completed_polynomial_coefficient_box_row_1 e
  · exact normalized_outer_completed_polynomial_coefficient_box_row_2 e
  · exact normalized_outer_completed_polynomial_coefficient_box_row_3 e
  · exact normalized_outer_completed_polynomial_coefficient_box_row_4 e
  · exact normalized_outer_completed_polynomial_coefficient_box_row_5 e
  · exact normalized_outer_completed_polynomial_coefficient_box_row_6 e
  · exact normalized_outer_completed_polynomial_coefficient_box_row_7 e
  · exact normalized_outer_completed_polynomial_coefficient_box_row_8 e
  · exact normalized_outer_completed_polynomial_coefficient_box_row_9 e
  · exact normalized_outer_completed_polynomial_coefficient_box_row_10 e
  · exact normalized_outer_completed_polynomial_coefficient_box_row_11 e
  · exact normalized_outer_completed_polynomial_coefficient_box_row_12 e

theorem normalized_outer_completed_polynomial_coefficient_box_calc_contains
    (n e : ℕ) :
    (normalizedOuterCompletedPolynomialCoefficientBoxCalc n e).Contains
      (normalizedOuterCompletedPolynomialCoefficient chartRatio (Real.log 3) n e) := by
  by_cases he : e ≤ n
  · rw [normalizedOuterCompletedPolynomialCoefficientBoxCalc, if_pos he]
    unfold normalizedOuterCompletedPolynomialCoefficient
    rw [if_pos he]
    apply exact_range_sum_box_contains
    intro g hg
    by_cases hge : e ≤ g
    · rw [if_pos hge]
      have hb := normalized_outer_base_polynomial_coefficient_box_contains
        g e
      have hgpoint := normalized_gamma_coefficient_point (n - g)
      have hm := Box.mul_contains hb hgpoint
      simpa [hge] using hm
    · rw [if_neg hge]
      simp [Box.point, Box.Contains, hge]
  · rw [normalizedOuterCompletedPolynomialCoefficientBoxCalc, if_neg he]
    unfold normalizedOuterCompletedPolynomialCoefficient
    rw [if_neg he]
    simp [Box.point, Box.Contains]

theorem normalized_outer_completed_polynomial_coefficient_box_contains
    (n e : ℕ) :
    (normalizedOuterCompletedPolynomialCoefficientBox n e).Contains
      (normalizedOuterCompletedPolynomialCoefficient chartRatio (Real.log 3) n e) := by
  have hcalc := normalized_outer_completed_polynomial_coefficient_box_calc_contains n e
  by_cases hn : n < 13
  · by_cases he : e < 13
    · have htable := normalized_outer_completed_polynomial_coefficient_box_table_bound
        ⟨n, hn⟩ ⟨e, he⟩
      have hout := Box.subset_contains htable hcalc
      simpa [normalizedOuterCompletedPolynomialCoefficientBox, hn, he] using hout
    · simpa [normalizedOuterCompletedPolynomialCoefficientBox, hn, he] using hcalc
  · simpa [normalizedOuterCompletedPolynomialCoefficientBox, hn] using hcalc


end
end C3CofactorCorrelation
