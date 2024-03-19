(declare-fun a_ack!71 () (_ BitVec 64))
(declare-fun FPCHECK_FDIV_UNDERFLOW
             ((_ FloatingPoint 11 53) (_ BitVec 64))
             Bool)
(assert (not (fp.lt (fp.abs ((_ to_fp 11 53) a_ack!71))
            ((_ to_fp 11 53) #x3f20000000000000))))
(assert (FPCHECK_FDIV_UNDERFLOW (fp.abs ((_ to_fp 11 53) a_ack!71)) #x3fe921fb54442d18))
