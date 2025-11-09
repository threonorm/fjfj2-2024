interface State#(type a);
    method Action _write(a val);
    method a _read ();
endinterface

// Placeholder to make compiler happy
module mkState#(a val)(State#(a));

    method Action _write(a val);
        noAction;
    endmethod : _write

    method a _read();
        return ?;
    endmethod : _read
endmodule : mkState
