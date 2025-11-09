import State :: *;
import FIFO :: *;


interface LossyMap#(type addr_t, type data_t);
    method Maybe#(data_t) lookup(addr_t a);
    method Action insert(addr_t a, data_t d);
endinterface


// Implemented with uninterpreted functions addr_t -> Maybe#(data_t)
// Self invalidating: there is a rule that downgrades automatically

module mkLossyMap(LossyMap#(addr_t, data_t)) provisos (Eq#(addr_t));
    function Maybe#(data_t) empty(addr_t a) = Invalid;

    State#(function Maybe#(data_t) m(addr_t a)) s <- mkState(empty);
    State#(addr_t) random_addr <- mkState(?);

    rule evict;
        let a = random_addr;
        function Maybe#(data_t) new_s(addr_t newa);
            if (a == newa) begin 
                return Invalid;
            end else begin 
                return s(newa);
            end
        endfunction
        s <= new_s;
    endrule : evict

    method Maybe#(data_t) lookup(addr_t a);
        return s(a);
    endmethod : lookup

    method Action insert(addr_t a, data_t d);
        function Maybe#(data_t) new_s(addr_t newa);
            if (a == newa) begin 
                return Valid(d);
            end else begin 
                return s(newa);
            end
        endfunction
        s <= new_s;
    endmethod : insert
endmodule

