(set-logic ALL)
(set-info :status unsat)
(declare-datatypes ((ap 0)) (((bp) (cp (p (_ BitVec 2)) (dp (_ BitVec 2))
  (leftp ap) (aap ap)))))
(declare-datatypes ((ep 0)) (((kp) (fp (jp ep) (gp (_ BitVec 2))))))
(declare-fun mp (ap) Bool)
(declare-fun op (ap) (_ BitVec 2))
(declare-fun abp1 () ap)
(declare-fun acp2 ((_ BitVec 2) ap) ap)
(declare-fun qp ((_ BitVec 2) ap ap) ap)
(declare-fun rp (ep ap) ap)
(declare-fun adp (ap ap) ap)
(declare-fun abp9 () ap)
(declare-sort sp 0)
(declare-fun mpae (sp) ap)
(declare-sort tp 0)
(declare-fun opu (tp) ap)
(declare-sort up2 0)
(declare-fun acp2v (up2) (_ BitVec 2))
(declare-fun acp2w (up2) ap)
(declare-fun qpag (up2) (_ BitVec 2))
(declare-fun qpah (up2) ap)
(declare-fun qpai (up2) ap)
(declare-fun adpan (up2) ap)
(declare-fun adpao (up2) ap)
(assert (forall ((i sp)) (= (mp (mpae i)) (ite ((_ is bp) (mpae i)) true (mp
  (aap (mpae i)))) true (ite ((_ is cp) (mpae i)) (exists ((z tp)) (= (opu z)
  (mpae i))) true))))
(assert (forall ((i up2)) (and (= (acp2w i) (adp abp9 (cp (_ bv1 2) (acp2v i)
  bp bp))) (exists ((z up2)) (and (= (adpao z) (acp2w i)) (= (adpan z) (cp (_
  bv1 2) (acp2v i) bp bp)))))))
(assert (forall ((i up2)) (and (exists ((z tp)) (= (opu z) (qpah i))) (exists
  ((z tp)) (= (opu z) (qpai i))) (= (qp (qpag i) (qpah i) (qpai i)) (ite
  (bvslt (op (qpah i)) (op (qpai i))) (cp (bvadd (op (qpai i)) (_ bv1 2))
  (qpag i) (qpah i) (qpai i)) (cp (bvadd (op (qpah i)) (_ bv1 2)) (qpag i)
  (qpai i) (qpah i)))))))
(assert (forall ((i up2)) (and (exists ((z up2)) (and (= (qpag z) (dp abp1))
  (= (qpah z) (leftp (adpan i))))) (= (adpao i) (ite ((_ is bp) (adpao i))
  (adpan i) (qp (dp abp9) (leftp (adpan i)) (adpao i)))))))
(assert (exists ((hp ap) (lp ep)) (not (=> (exists ((z sp)) (= hp (mpae z)))
  (or (forall ((z up2)) (not (= hp (acp2w z)))) (mp (ite ((_ is kp) lp) hp (rp
  (jp lp) (acp2 (gp lp) hp)))) (forall ((z sp)) (not (= (mpae z) (ite ((_ is
  kp) lp) hp (rp (jp lp) (acp2 (gp lp) hp)))))))))))
(check-sat)
