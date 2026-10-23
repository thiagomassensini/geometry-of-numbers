from pathlib import Path
from fractions import Fraction as Q
import importlib.util,math,re,json
p=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('boxes',p/'interval_data.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
logs=[m.wider(m.log_(Q(n),n.bit_length())) for n in range(1,206)]
amps=[m.wider(m.exp_(m.mul(m.point(Q(-1,2)),a))) for a in logs]
def wave(n,r):return m.mul(amps[n-1],m.mul(m.pow_(m.neg(logs[n-1]),r),m.point(Q(1,math.factorial(r)))))
w=[Q(728,729),Q(-1444,729),Q(638,729),Q(364,243),Q(-815,243),Q(880,243),Q(-637,243),Q(329,243),Q(-121,243),Q(91,729),Q(-14,729),Q(1,729)]
def head(r):return m.add(m.add(m.point(1 if r==0 else 0),m.sum_(m.add(m.sub(wave(3*k+2,r),m.mul(m.point(2),wave(3*k+3,r))),wave(3*k+4,r)) for k in range(64))),m.sum_(m.mul(m.point(v),wave(194+k,r)) for k,v in enumerate(w)))
H=[m.wider(head(r),22) for r in range(7)]
pl=(m.log_(Q(314159265358979323846,10**20),2)[0],m.log_(Q(314159265358979323847,10**20),2)[1]);pl=m.wider(pl)
ea=m.wider(m.exp_(m.mul(m.point(Q(-1,4)),pl)))
l3=logs[2];ca=m.wider(m.exp_(m.mul(m.point(Q(1,2)),l3)))
P=[m.point(Q(-1,8) if r==0 else Q(1,2) if r==2 else 0) for r in range(7)]
E=[m.mul(ea,m.mul(m.pow_(m.mul(m.point(Q(-1,2)),pl),r),m.point(Q(1,math.factorial(r))))) for r in range(7)]
C=[m.sub(m.point(1 if r==0 else 0),m.mul(ca,m.mul(m.pow_(m.neg(l3),r),m.point(Q(1,math.factorial(r)))))) for r in range(7)]
R=[]
for n in range(7):R.append(m.inv(C[0]) if n==0 else m.mul(m.neg(m.sum_(m.mul(R[j],C[n-j]) for j in range(n))),m.inv(C[0])))
def conv(a,b):return [m.sum_(m.mul(a[j],b[r-j]) for j in range(r+1)) for r in range(7)]
L=conv(conv(conv(P,E),R),H)
gtext=(p.parent/'c3-gamma-jet-enclosures/LogGammaData.lean').read_text();gg=list(map(Q,re.search(r'gammaRealReference[^\n]*:= !\[([^\]]+)\]',gtext)[1].split(',')))
F=conv(L,[m.point(q) for q in gg]);qs=[Q(497120778188314,10**15),Q(-11485972157573,10**15),Q(123452018070,10**15),Q(-832355481,10**15)]
for j in range(4):
 a=F[2*j];a=a if j%2==0 else m.neg(a)
 print(2*j, tuple(map(float,a)), 'error',float(max(abs(a[0]-qs[j]),abs(a[1]-qs[j]))),'width',float(a[1]-a[0]))
 assert max(abs(a[0]-qs[j]),abs(a[1]-qs[j]))<=Q(1,10**13)
text=['import FiniteCoefficientBoxes','namespace CarryC3Boxes','open CarryC3Tail CarryC3Gamma','open scoped BigOperators','set_option maxHeartbeats 10000000','set_option maxRecDepth 20000','def headReferenceBox (r : Fin 7) : Box := !['+','.join(map(m.leanbox,H))+'] r',
 'theorem head_evaluator_check (r : Fin 7) : (headJetBox r.val).Subset (headReferenceBox r) := by',
 '  fin_cases r <;> decide +kernel',
 'theorem head_reference_contains (r : Fin 7) : (headReferenceBox r).Contains (headRealJet 64 r.val) :=',
 '  Box.subset_contains (head_evaluator_check r) (head_jet_box r.val)',
 'def cachedHeadJetBox (r : ℕ) : Box := if h:r<7 then headReferenceBox ⟨r,h⟩ else headJetBox r',
 'theorem cached_head_contains (r : ℕ) : (cachedHeadJetBox r).Contains (headRealJet 64 r) := by',
 '  unfold cachedHeadJetBox',
 '  split_ifs with h',
 '  · exact head_reference_contains ⟨r,h⟩',
 '  · exact head_jet_box r',
 'def cachedLeftJetBox : ℕ → Box := convolutionBox',
 '  (convolutionBox (convolutionBox polynomialJetBox exponentialJetBox) (reciprocalJetBox chartJetBox)) cachedHeadJetBox',
 'def cachedCompletedJetBox (r : Fin 7) : Box := bsumFin (fun j : Fin (r.val+1) =>',
 '  bmul (cachedLeftJetBox j.val) (Box.point (gammaRealReference ⟨r.val-j.val,by omega⟩)))',
 'theorem cached_left_contains (r : ℕ) : (cachedLeftJetBox r).Contains (leftRealJet r) :=',
 '  convolution_box _ _ _ _ (convolution_box _ _ _ _',
 '    (convolution_box _ _ _ _ polynomial_jet_box exponential_jet_box)',
 '    (reciprocal_jet_box chartJetBox chartRealJet chart_jet_box (Or.inr chart_center_interval_negative))) cached_head_contains r',
 'theorem cached_completed_contains (r : Fin 7) : (cachedCompletedJetBox r).Contains (finiteCompletedRealJet r) := by',
 '  have hh := bsumFin_contains',
 '    (fun j : Fin (r.val+1) => bmul (cachedLeftJetBox j.val) (Box.point (gammaRealReference ⟨r.val-j.val,by omega⟩)))',
 '    (fun j : Fin (r.val+1) => leftRealJet j.val*(gammaRealReference ⟨r.val-j.val,by omega⟩:ℝ))',
 '    (fun j => bmul_contains (cached_left_contains j.val) (Box.point_contains _))',
 '  have he : (∑ j : Fin (r.val+1), leftRealJet j.val*(gammaRealReference ⟨r.val-j.val,by omega⟩:ℝ))=finiteCompletedRealJet r :=',
 '    by',
 '      rw [Finset.sum_fin_eq_sum_range]',
 '      apply Finset.sum_congr rfl',
 '      intro j hj',
 '      simp only [Finset.mem_range.mp hj,dif_pos]',
 '  rw [he] at hh',
 '  exact hh',
 'end CarryC3Boxes']
a=text.index('theorem head_reference_contains (r : Fin 7) : (headReferenceBox r).Contains (headRealJet 64 r.val) :=')
(p/'HeadEvaluatorData.lean').write_text('\n'.join(text[:a]+['end CarryC3Boxes'])+'\n')
(p/'evidence').mkdir(exist_ok=True)
(p/'evidence/interval-generator-regression.json').write_text(json.dumps({'head_boxes':[[str(x) for x in a] for a in H],'finite_F_boxes':[[str(x) for x in a] for a in F],'source':'exact Fraction interval evaluation; Lean inclusion still required'},indent=2)+'\n')
