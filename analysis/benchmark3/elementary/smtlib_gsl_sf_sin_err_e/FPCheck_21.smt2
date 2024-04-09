(declare-fun a_ack!37 () (_ BitVec 64))
(declare-fun FPCHECK_FMUL_OVERFLOW ((_ FloatingPoint 11 53) (_ BitVec 64)) Bool)
(declare-fun b_ack!36 () (_ BitVec 64))
(declare-fun CF_cos ((_ BitVec 64)) (_ FloatingPoint 11 53))
(assert (fp.lt (fp.abs ((_ to_fp 11 53) a_ack!37)) ((_ to_fp 11 53) #x3f20000000000000)))
(assert (FPCHECK_FMUL_OVERFLOW (CF_cos a_ack!37) b_ack!36))