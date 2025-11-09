import State :: *;
import FIFO :: *;
import LossyMap :: *;
import Util :: *;

typedef enum {Ld, St} MemOp deriving (FShow, Bits, Eq);
typedef Bit#(32) Addr;
typedef Bit#(32) Data;
typedef Bit#(32) Id;

typedef struct { 
    MemOp mem_op;
    Id id;
    Addr addr;
    Data data;
} Req deriving (FShow, Bits, Eq);

typedef struct {
    Addr addr;
    Data data;
    Id id;
} Resp deriving (FShow, Bits, Eq);
// The top level interface that we care about is the interface showing the MMIO
// req/resp traces.
interface Mmio;
    method Req req;
    method Action deq_req();
    method Action resp(Resp r);
endinterface

// A processor implements two interfaces, an interface of kind MMIOToplevel, for
// outside world interaction, and an interface with memory
interface Processor_to_memory;
    method Req req;
    method Action deq_req();
    method Action resp(Resp r);
endinterface

interface Processor;
    interface Mmio ext; 
    interface Processor_to_memory mem; 
endinterface 

// A memory implements
interface Memory_to_processor;
    method Action req(Req r);
    method Action deq_resp();
    method Resp resp();
endinterface

// This module connects a processor and a memory together
module mkSOC#(module#(Processor) mkProc, module#(Memory_to_processor) mkMem)(Mmio);
    Processor proc <- mkProc;
    Memory_to_processor mem <- mkMem;

    rule req_proc_to_mem;
        proc.mem.deq_req();
        let r = proc.mem.req();
        mem.req(r);
    endrule : req_proc_to_mem 

    rule resp_mem_to_proc;
        mem.deq_resp();
        let r = mem.resp();
        proc.mem.resp(r);
    endrule : resp_mem_to_proc

    method Req req();
        return proc.ext.req();
    endmethod : req
    
    method Action deq_req();
        proc.ext.deq_req();
    endmethod : deq_req

    method Action resp(Resp r);
        proc.ext.resp(r);
    endmethod : resp
endmodule : mkSOC

// We give two implementations of memory
typedef function Data mem(Addr addr) UninterpretedMem;
function Data mem_init(Addr addr)=0;

// Memory, I can refine it independently, and write a cached memory
module mkMemSpec(Memory_to_processor);
    State#(UninterpretedMem) mem <- mkState(mem_init);
    FIFO#(Resp) resp_queue <- mkFIFO;

    method Action req(Req r);
        if (r.mem_op matches tagged Ld) begin 
            // It's a read, we can answer
            resp_queue.enq(Resp{
                addr : r.addr,
                data : mem(r.addr),
                id : r.id
            });
        end
        else begin 
            // It's a write, we update the memory
            function Data new_mem(Addr addr) = (addr == r.addr) ? r.data : mem(addr);
            mem <= new_mem;
        end
    endmethod : req

    method Action deq_resp();
        resp_queue.deq();
    endmethod : deq_resp

    method Resp resp();
        return resp_queue.first();
    endmethod : resp 
endmodule : mkMemSpec

typedef Bit#(5) Idx_reg;
typedef enum {Fetch, Decode, Execute, Writeback} Spec_state deriving (Eq, FShow, Bits);
(* noinline *)
function Bit#(5) rs1_of(Bit#(32) i)=?;
(* noinline *)
function Bit#(5) rs2_of(Bit#(32) i)=?;
(* noinline *)
function Bit#(5) rd_of(Bit#(32) i)=?;
(* noinline *)
function Bit#(32) arith(Bit#(32) i, Bit#(32) rs1, Bit#(32) rs2)=?;
// assume that craft_mem return a request with id = 0
(* noinline *)
function Req craft_mem(Bit#(32) i, Bit#(32) rs1)=?;
(* noinline *)
function Req craft_mmio(Bit#(32) i, Bit#(32) rs1)=?;
(* noinline *)
function Bit#(32) target(Bit#(32) i, Bit#(32) pc, Bit#(32) rs1, Bit#(32) rs2)=?;

(* noinline *)
function Bool inst_write(Bit#(32) i)=?;
(* noinline *)
function Bool is_mem_op(Bit#(32) i)=?;
(* noinline *)
function Bool is_mmio_op(Bit#(32) i)=?;
(* noinline *)
function Bool is_load_op(Bit#(32) i)=?;
(* noinline *)
function Bool change_cf(Bit#(32) i)=?;

interface Rf#(numeric type n, type a);
    method a read1(Bit#(n) i);
    method a read2(Bit#(n) i);
    method Action write(Bit#(n) i, a data);
endinterface

module mkRf(Rf#(5,Bit#(32)));
endmodule

(* synthesize *)
module mkSpecializedMap(LossyMap#(Bit#(32), Bit#(32)));
    let m <- mkLossyMap(); 
    return m;
endmodule
(* synthesize *)
module mkSpecializedRf(Rf#(5,Bit#(32)));
    Rf#(5, Bit#(32)) rf <- mkRf();
    return rf;
endmodule

module mkSpecProc(Processor);
    Reg#(Addr) pc <- mkReg(0); 
    Rf#(5, Bit#(32)) rf <- mkSpecializedRf();

    LossyMap#(Bit#(32), Bit#(32)) map <- mkSpecializedMap;

    FIFO#(Req) to_mem <- mkFIFO;
    FIFO#(Resp) from_mem <- mkFIFO;

    FIFO#(Req) to_mmio<- mkFIFO;
    FIFO#(Resp) from_mmio <- mkFIFO;

    // microarchitectural state 
    Reg#(Data) inst <- mkReg(0);
    Reg#(Data) rs1 <- mkReg(0);
    Reg#(Data) rs2 <- mkReg(0);
    Reg#(Data) rd <- mkReg(0);
    Reg#(Addr) next_pc <- mkReg(0);
    Reg#(Spec_state) state <- mkReg(Fetch);
    
    // The following two rules are the Non-Deterministic Load Machine, it emits ld for id > 0
    rule emit_fake_req;
        let r_id = ?; // r_id > 0
        let r_addr = ?; // r_id > 0
        to_mem.enq(Req{mem_op : Ld, addr : r_addr, id : r_id,  data : ?});
    endrule

    rule drain_fake_resp if (from_mem.first() matches .r &&& r.id > 0);
        // Drain responses if they were destined to the NDLM
        from_mem.deq();
    endrule

    rule do_fetch (state == Fetch);
        next_pc <= pc + 4;
        let res = map.lookup(pc);
        if (isValid(res)) begin 
            from_mem.enq(Resp{data : fromMaybe(?, res), id : 0, addr:pc});
        end else begin 
            to_mem.enq(Req{mem_op : Ld, addr : pc, data : ?, id : 0});
        end
        state <= Decode;
    endrule : do_fetch

    rule do_decode ( state == Decode &&& from_mem.first() matches .r &&& r.id == 0 );
        let resp = from_mem.first();
        let data_inst = resp.data;
        inst <= data_inst;
        from_mem.deq();
        rs1 <= rf.read1(rs1_of(data_inst));
        rs2 <= rf.read2(rs2_of(data_inst));
        state <= Execute;
    endrule : do_decode

    rule do_execute ( state == Execute );
        if (change_cf(inst)) begin
            next_pc <= target(inst, pc, rs1,rs2);
        end
        rd <= arith(inst, rs1, rs2);
        if (is_mem_op(inst)) begin
            let req = craft_mem(inst,rs1);
            let res = map.lookup(req.addr);
            if (isValid(res) && req.mem_op == Ld) begin 
                from_mem.enq(Resp{data : fromMaybe(?, res), id : 0, addr:req.addr});
            end else begin 
                to_mem.enq(craft_mem(inst,rs1));
            end
        end else begin 
        if (is_mmio_op(inst)) begin
            to_mem.enq(craft_mmio(inst,rs1));
        end end
        state <= Writeback;
    endrule : do_execute

    Bool received_data_load = from_mem.first().id == 0;

    rule do_writeback ( state == Writeback
                        && implies(is_load_op(inst), received_data_load));
        let new_val = rd;
        if (is_load_op(inst)) begin 
            new_val = to_mem.first().data;
            to_mem.deq();
        end
        if (inst_write(inst)) begin
            rf.write(rd_of(inst), new_val);
        end
        state <= Fetch;
    endrule : do_writeback

    interface Processor_to_memory mem;
        method Req req();
            return to_mem.first();
        endmethod : req

        method Action deq_req();
            to_mem.deq();
        endmethod : deq_req

        method Action resp(Resp r);
            map.insert(r.addr, r.data);
            from_mem.enq(r);
        endmethod : resp
    endinterface

    interface Mmio ext;
        method Req req();
            return to_mmio.first();
        endmethod : req

        method Action deq_req();
            to_mmio.deq();
        endmethod : deq_req

        method Action resp(Resp r);
            from_mmio.enq(r);
        endmethod : resp
    endinterface
endmodule : mkSpecProc


module mkDecoupledProc(Processor);
    Reg#(Addr) next_pc <- mkReg(0);
    Reg#(Addr) pc <- mkReg(0);
    // Next pc 

    Rf#(5, Bit#(32)) rf <- mkRf();

    LossyMap#(Bit#(32), Bit#(32)) map <- mkLossyMap;

    FIFO#(Req) to_mem <- mkFIFO;
    FIFO#(Resp) from_mem <- mkFIFO;

    FIFO#(Req) to_mmio<- mkFIFO;
    FIFO#(Resp) from_mmio <- mkFIFO;

    // microarchitectural state 
    Reg#(Data) inst <- mkReg(0);
    Reg#(Data) rs1 <- mkReg(0);
    Reg#(Data) rs2 <- mkReg(0);
    Reg#(Data) rd <- mkReg(0);
    Reg#(Spec_state) state <- mkReg(Decode);

    // The following two rules are the Non-Deterministic Load Machine, it emits ld for id > 0
    rule emit_fake_req;
        let r_id_gt2 = ?; // r_id > 2
        to_mem.enq(Req{mem_op : Ld, addr : next_pc, id : r_id_gt2,  data : ?});
    endrule

    rule drain_fake_resp if (from_mem.first() matches .r &&& r.id > 2);
        // Drain requests if they were destined to the NDLM
        to_mem.deq();
    endrule

    rule do_fetch;
        let r_addr = ?;
        next_pc <= r_addr; 
        let res = map.lookup(next_pc);
        if (isValid(res)) begin 
            // We need to keep tabs on this request we just sent
            from_mem.enq(Resp{data : fromMaybe(?, res), id : 1, addr:pc});
        end else begin 
            to_mem.enq(Req{mem_op : Ld, addr : next_pc, data : ?, id:1});
        end
    endrule : do_fetch

    Resp received_resp = from_mem.first();
    Bool is_still_available = isValid(map.lookup(received_resp.addr)) ;
    Bool expected_instruction = received_resp.addr == pc && received_resp.id == 1;

    rule do_decode (state == Decode && is_still_available && expected_instruction);
        let data_inst = received_resp.data;
        from_mem.deq();
        inst <= data_inst;
        rs1 <= rf.read1(rs1_of(data_inst));
        rs2 <= rf.read2(rs2_of(data_inst));
        state <= Execute;
    endrule : do_decode

    rule do_decode_drop (state == Decode && (!expected_instruction || !is_still_available));
        from_mem.deq();
    endrule : do_decode_drop

    rule do_execute ( state == Execute );
        if (change_cf(inst)) begin
            pc <= target(inst, pc, rs1,rs2);
        end
        else pc <= pc + 4;
        rd <= arith(inst, rs1, rs2);
        if (is_mem_op(inst)) begin
            let req = craft_mem(inst,rs1);
            let res = map.lookup(req.addr);
            if (isValid(res) && req.mem_op == Ld) begin 
                from_mem.enq(Resp{data : fromMaybe(?, res), id:2, addr:req.addr});
            end else begin 
                to_mem.enq(craft_mem(inst,rs1));
            end
        end
        if (is_mmio_op(inst)) begin
            to_mem.enq(craft_mmio(inst,rs1));
        end
        state <= Writeback;
    endrule : do_execute

    Bool received_data_load = from_mem.first().id == 2;

    rule do_writeback (state == Writeback &&
                       implies(is_load_op(inst), received_data_load));
        let new_val = rd;
        if (is_load_op(inst)) begin 
            new_val = to_mem.first().data;
            to_mem.deq();
        end
        if (inst_write(inst)) begin
            rf.write(rd_of(inst), new_val);
        end
        state <= Decode;
    endrule : do_writeback

    interface Processor_to_memory mem;
        method Req req();
            return to_mem.first();
        endmethod : req

        method Action deq_req();
            to_mem.deq();
        endmethod : deq_req

        method Action resp(Resp r);
            map.insert(r.addr, r.data);
            from_mem.enq(r);
        endmethod : resp
    endinterface

    interface Mmio ext;
        method Req req();
            return to_mmio.first();
        endmethod : req

        method Action deq_req();
            to_mmio.deq();
        endmethod : deq_req

        method Action resp(Resp r);
            from_mmio.enq(r);
        endmethod : resp
    endinterface
endmodule : mkDecoupledProc

