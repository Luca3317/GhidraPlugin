package analysis;
import ghidra.program.model.pcode.HighFunction;
import ghidra.program.model.pcode.HighVariable;
import ghidra.program.model.pcode.PcodeBlockBasic;

public interface EdgeCondition {
	
	/**
	 * Returns {@code true} if the block src leads to block dest under a given condition. Said condition needs to be hardcoded in each implementation of check.
	 * @param func
	 * @param src
	 * @param dest
	 * @param var
	 * @param obj Additional object in case other arguments are needed.
	 * @return
	 */
	boolean check(HighFunction func, PcodeBlockBasic src, PcodeBlockBasic dest, HighVariable var, Object obj);
}
