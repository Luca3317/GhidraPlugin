package analysis;


import ghidra.program.model.pcode.HighVariable;
import ghidra.program.model.pcode.PcodeBlockBasic;
import ghidra.program.model.pcode.PcodeOpAST;

public interface ReassignmentCondition {
	
	/**
	 * Checks if the variable is reassigned within the block, in a relevant way.
	 * Returns 1 if (one of) the variable(s) has been reassigned within the block so that reaching this block is inherently vulnerable.
	 * Returns -1 if (one of) the variable(s) has been reassigned within the block so that reaching this block is inherently safe (at least excluding following blocks).
	 * Returns 0 if none of the variables have changed in a relevant way.
	 * For example, if a pointer is assigned null, the branch conditions from the inflowing blocks checking if the pointer is null become irrelevant.
	 * @param func
	 * @param block
	 * @param var
	 * @param obj
	 * @return
	 */
	int check(PcodeBlockBasic block, HighVariable var, Object obj, PcodeOpAST op);
}
