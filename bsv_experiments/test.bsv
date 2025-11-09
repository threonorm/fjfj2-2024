
interface Foo;
	method Action yo(Bit#(32) b);
	method Bit#(32) bar(Bit#(32) a);
endinterface

(* synthesize *)
module mkTest(Foo);
	Reg#(Bit#(32)) a <- mkReg(0);

	rule test;
		if (a == 0) begin 
		a <= a +2;
		end
	endrule

	method Action yo(Bit#(32) b);
		if (a ==2) begin 
		a <= b; end
		else a <= 2;
			
	endmethod

	method Bit#(32) bar(Bit#(32) z);
		return (z + a);
	endmethod

endmodule

