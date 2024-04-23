package analysis;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import ghidra.app.util.importer.MessageLog;
import ghidra.program.model.pcode.HighFunction;
import ghidra.program.model.pcode.HighVariable;
import ghidra.program.model.pcode.PcodeBlockBasic;
import ghidra.program.model.pcode.PcodeOp;
import ghidra.program.model.pcode.PcodeOpAST;
import ghidra.program.model.pcode.VarnodeAST;
import ghidra.util.Msg;
import ghidra.util.exception.CancelledException;
import ghidra.util.task.TaskMonitor;

public class BufferOverflowAnalyzer extends VulnerabilityDetectionAnalyzerComponent {

	/**
	 * - get all offset store instructions
	 * - check for each if in loop (if not, remove)
	 * - check if offset modified during loop (if not, remove)
	 * - for rest: exact same as ooba
	 */
	
	@Override
	protected void analyzeFunction(HighFunction func, TaskMonitor monitor, MessageLog log, boolean preferFalseNegatives) throws CancelledException {
					
		//sief(func);
		
		Set<HighVariable> params = VulnerabilityDetectionUtils.getParameters(func);
		
		// Get offset dereferenced, only STORE instructions
		Set<PcodeOpAST> derefs = VulnerabilityDetectionUtils.getDereferencingInstructions(func);
		derefs.removeAll(VulnerabilityDetectionUtils.getDirectlyDereferencingInstructions(func));
		
		Set<PcodeOpAST> derefsIterate = new LinkedHashSet<PcodeOpAST>(derefs);
				
				
		for (PcodeOpAST op : derefsIterate)
			if (op.getOpcode() == PcodeOp.LOAD)
				derefs.remove(op);
		
		for (PcodeOpAST op : derefsIterate) {
			
			Set<HighVariable> contained = VulnerabilityDetectionUtils.getContainedVars(func, (VarnodeAST) op.getInput(1));
			Set<HighVariable> pointers = new LinkedHashSet<HighVariable>();
			Set<HighVariable> nonPointers = new LinkedHashSet<HighVariable>();
			Set<HighVariable> unknowns = new LinkedHashSet<HighVariable>();
					
			// Populate the lists
			for (HighVariable var : contained) {
				
				int pointer = VulnerabilityDetectionUtils.isPointer(var);
				
				if (pointer == 0)
					nonPointers.add(var);
				else if (pointer == 1)
					pointers.add(var);
				else
					unknowns.add(var);
			}

			Set<HighVariable> checking = new LinkedHashSet<HighVariable>(pointers);
			checking.addAll(unknowns);
			
			for (HighVariable ptr : checking) {
			
				Set<HighVariable> offset = getOffset(ptr, (VarnodeAST) op.getInput(1));
				
				for (HighVariable var : offset) {
					
					Set<HighVariable> set = new LinkedHashSet<HighVariable>();
					if (preferFalseNegatives)
						set.add(var);
					else
						set.addAll(offset);
				
					if (!loopAndModified(func, op, set))
						continue;		
					
					
					// Potential "too-large" test
					edgeCond = (a, b, c, d, e) -> { return leadsToIfLarge(a, b, c, d, e); };
					reassCond = (a, b, c, d) -> { return relevantReassignedPositive(a, b, c, d); };
					
					if (reachableIf(op, func, func.getBasicBlocks().get(0), ptr, set, true, new HashMap<PcodeBlockBasic, Integer>(), new HashMap<PcodeBlockBasic, Integer>())) {
						
						if (params.contains(ptr))
							results.addPotential(ptr);
						else
							results.addInherent(ptr);
						
						break;
					}	
				}
			}				
		}
	}
	
	
		
	
	
	
	
	private boolean leadsToIfLarge(HighFunction func, PcodeBlockBasic src, PcodeBlockBasic dest, HighVariable ptr, Object offset) {
		
		@SuppressWarnings("unchecked")
		LinkedHashSet<HighVariable> offsetSet = (LinkedHashSet<HighVariable>) offset;
		
		Set<HighVariable> params = VulnerabilityDetectionUtils.getParameters(func);
		Set<HighVariable> locals = VulnerabilityDetectionUtils.getLocalVariables(func);
		
		Iterator<PcodeOp> ops = src.getIterator();
		
		PcodeOp lastPc = null;
		
		// Get last instruction in block
		while (ops.hasNext())	
			lastPc = ops.next();
		
		// If not conditional => true
		// If not flag thats is checked => Dont think this is even possible => true
		if (lastPc.getOpcode() != PcodeOp.CBRANCH)
			return true;
		
		PcodeOp def = lastPc.getInput(1).getDef();
		
		// pointless i think
		if (def == null) {
			Msg.out("\n" + func.getFunction().getName() + " Block " + src.getStart());
			Msg.out("Flag never set?");
			return true;
		}
		
		/**
		 * Potential "too-large" check
		 * Relevant instructions
		 * INT_LESS, INT_SLESS, INT_LESSEQUAL, INT_SLESSEQUAL, FLOAT_LESS, FLOAT_LESSEQUAL
		 * INT_EQUAL, INT_COPY
		 */
				
		int defOpcode = def.getOpcode();
		
		VarnodeAST input0 = (VarnodeAST) def.getInput(0);
		VarnodeAST input1 = (VarnodeAST) def.getInput(1);
		
		VarnodeAST offsetNode = null;
		VarnodeAST otherNode = null;
		
		// check not good enough yet
		if (VulnerabilityDetectionUtils.getContainedVars(func, input0).containsAll(offsetSet)) {
			offsetNode = input0;
			otherNode = input1;
		}
		else if (VulnerabilityDetectionUtils.getContainedVars(func, input1).containsAll(offsetSet)) {
			offsetNode = input1;
			otherNode = input0;
		}
			
		// If offsets irrelevant
		if (offsetNode == null)
			return true;
		
		boolean leadsTo = true;
				
		if (lessInstrs.contains(defOpcode)) {
			
			// if smaller than other
			if (offsetNode.equals(input0)) {
				
				// constant check
				if (otherNode.isConstant()) {
					if (otherNode.getOffset() <= 1)
						if (dest.getStart().equals(src.getTrueOut().getStart()))
							leadsTo = false;
				}
				// var check
				else {
					
					// if consists entirely of param
					if (params.containsAll(VulnerabilityDetectionUtils.getContainedVars(func, otherNode))) {

						if (params.contains(ptr))
							if (dest.getStart().equals(src.getTrueOut().getStart()))
								leadsTo = false;
						
					}
					// if consists entirely of locals
					else if (locals.containsAll(VulnerabilityDetectionUtils.getContainedVars(func, otherNode))) {
						
						if (locals.contains(ptr))
							if (dest.getStart().equals(src.getTrueOut().getStart()))
								leadsTo = false;
					
					}
				}
			}
			// if larger than
			else {
				
				// constant check
				if (otherNode.isConstant()) {
					if (otherNode.getOffset() <= 0)
						if (dest.getStart().equals(src.getFalseOut().getStart()))
							leadsTo = false;
				}
				// var check
				else {
				
					// if consists entirely of param
					if (params.containsAll(VulnerabilityDetectionUtils.getContainedVars(func, otherNode))) {

						if (params.contains(ptr))
							if (dest.getStart().equals(src.getFalseOut().getStart()))
								leadsTo = false;
						
					}
					// if consists entirely of locals
					else if (locals.containsAll(VulnerabilityDetectionUtils.getContainedVars(func, otherNode))) {
						
						if (locals.contains(ptr))
							if (dest.getStart().equals(src.getFalseOut().getStart()))
								leadsTo = false;
					}
				}
			}
		}
		
		else if (lessEqualInstrs.contains(defOpcode)) {
			
			// if smallerequal than other
			if (offsetNode.equals(input0)) {
				
				// constant check
				if (otherNode.isConstant()) {
					if (otherNode.getOffset() <= 0)
						if (dest.getStart().equals(src.getTrueOut().getStart()))
							leadsTo = false;
				}
				// var check
				else {
					
					// if consists entirely of param
					if (params.containsAll(VulnerabilityDetectionUtils.getContainedVars(func, otherNode))) {

						if (params.contains(ptr))
							if (dest.getStart().equals(src.getTrueOut().getStart()))
								leadsTo = false;
						
					}
					// if consists entirely of locals
					else if (locals.containsAll(VulnerabilityDetectionUtils.getContainedVars(func, otherNode))) {
						
						if (locals.contains(ptr))
							if (dest.getStart().equals(src.getTrueOut().getStart()))
								leadsTo = false;
					
					}
				}
			}
			// if largerequal than
			else {
				
				// constant check
				if (otherNode.isConstant()) {
					if (otherNode.getOffset() <= 1)
						if (dest.getStart().equals(src.getFalseOut().getStart()))
							leadsTo = false;
				}
				// var check
				else {
				
					// if consists entirely of param
					if (params.containsAll(VulnerabilityDetectionUtils.getContainedVars(func, otherNode))) {

						if (params.contains(ptr))
							if (dest.getStart().equals(src.getFalseOut().getStart()))
								leadsTo = false;
						
					}
					// if consists entirely of locals
					else if (locals.containsAll(VulnerabilityDetectionUtils.getContainedVars(func, otherNode))) {
						
						if (locals.contains(ptr))
							if (dest.getStart().equals(src.getFalseOut().getStart()))
								leadsTo = false;
					}
				}
			}
		}
		
		else if (equalInstr.contains(defOpcode)) {
		
			// constant check
			if (otherNode.isConstant()) {
				if (otherNode.getOffset() <= 0)
					if (dest.getStart().equals(src.getTrueOut().getStart()))
						leadsTo = false;			
			}
			
			// var check
			else {
							
				// if consists entirely of param
				if (params.containsAll(VulnerabilityDetectionUtils.getContainedVars(func, otherNode))) {

					if (params.contains(ptr))
						if (dest.getStart().equals(src.getTrueOut().getStart()))
							leadsTo = false;
								
				}
				// if consists entirely of locals
				else if (locals.containsAll(VulnerabilityDetectionUtils.getContainedVars(func, otherNode))) {
								
					if (locals.contains(ptr))
						if (dest.getStart().equals(src.getTrueOut().getStart()))
							leadsTo = false;
								
				}
			}
		}
		
		else if (notEqualInstr.contains(defOpcode)) {
			
			// constant check
			if (otherNode.isConstant()) {
				if (otherNode.getOffset() <= 0)
					if (dest.getStart().equals(src.getFalseOut().getStart()))
						leadsTo = false;			
			}
						
			// var check
			else {
										
				// if consists entirely of param
				if (params.containsAll(VulnerabilityDetectionUtils.getContainedVars(func, otherNode))) {

					if (params.contains(ptr))
						if (dest.getStart().equals(src.getFalseOut().getStart()))
							leadsTo = false;
											
				}
				// if consists entirely of locals
				else if (locals.containsAll(VulnerabilityDetectionUtils.getContainedVars(func, otherNode))) {
											
					if (locals.contains(ptr))
						if (dest.getStart().equals(src.getFalseOut().getStart()))
							leadsTo = false;
											
				}
			}
		}
		
		
		return leadsTo;
	}
	
	protected int relevantReassignedPositive(PcodeBlockBasic block, HighVariable var, Object offset, PcodeOpAST pcode) {
		
		@SuppressWarnings("unchecked")
		LinkedHashSet<HighVariable> offsetSet = (LinkedHashSet<HighVariable>) offset;
				
		List<PcodeOp> ops = new ArrayList<PcodeOp>();
		block.getIterator().forEachRemaining(ops::add);
			
		Collections.reverse(ops);
		
		int changedAfter = 0;
		if (block.equals(pcode.getParent())) {
		
			List<PcodeOp> tmpIter = new ArrayList<PcodeOp>(ops);
			for (PcodeOp op : tmpIter) {
				
				ops.remove(op);
				if (op.equals(pcode))
					break;
				
				PcodeOpAST opAST = (PcodeOpAST) op;
				
				if (!opAST.isAssignment())
					continue;
				
				VarnodeAST output = (VarnodeAST) opAST.getOutput();

				if (!Arrays.asList(var.getInstances()).contains(output))
					continue;
				
				int res = actualLargeValueCheck(opAST, output, var, 0);
				
				if (res != 0)
					changedAfter = res * 10;
				
				if (changedAfter != 0)
					break;
			}
		}
		
		for (PcodeOp op : ops) {
			
			PcodeOpAST opAST = (PcodeOpAST) op;
			
			if (!opAST.isAssignment())
				continue;
			
			VarnodeAST output = (VarnodeAST) opAST.getOutput();

			if (!VulnerabilityDetectionUtils.getContainedVars(var.getHighFunction(), output).containsAll(offsetSet))
				continue;
			
			int res = actualLargeValueCheck(opAST, output, var, 0);
			
			if (res != 0)
				return res;
		}
		
		return changedAfter;
	}
	
	private int actualLargeValueCheck(PcodeOpAST opAST, VarnodeAST output, HighVariable var, int iter) {
		
		if (iter > calcDepth)
			return 0;
		
		VarnodeAST input0 = (VarnodeAST) opAST.getInput(0);
		VarnodeAST input1 = (VarnodeAST) opAST.getInput(1);
		
		if (opAST.getOpcode() == PcodeOp.COPY) {
						
			// const check
			if (input0.isConstant()) {
				
				if (input0.getOffset() >= 1)
					return 1;
				
				return -1;
			}
		}
		else if (addInstrs.contains(opAST.getOpcode())) {
			
			if (input0.isConstant()) {
				
				if (input1.isConstant()) {
					
					if (input0.getOffset() + input1.getOffset() >= 1)
						return 1;
					
					return -1;
				}					
			}
			
			// if is incremented
			if (Arrays.asList(var.getInstances()).contains(input0) || Arrays.asList(var.getInstances()).contains(input1))	
				return 1;
		}
		else if (subInstrs.contains(opAST.getOpcode())) {
			
			if (input0.isConstant()) {
				
				if (input1.isConstant()) {
					
					if (input0.getOffset() - input1.getOffset() >= 1)
						return 1;
					
					return -1;
				}					
			}
		}
		else if (multInstrs.contains(opAST.getOpcode()) || divInstrs.contains(opAST.getOpcode())) {
			
			if (input0.isConstant()) {
				
				if (input1.isConstant()) {
					
					if (input0.getOffset() * input1.getOffset() >= 1)
						return 1;
					
					return -1;
				}					
			}
		}
		else if (opAST.getOpcode() == PcodeOp.MULTIEQUAL) {
			
			boolean allSafe = true;
			for (int i = 0; i < opAST.getNumInputs(); i++) {
								
				PcodeOpAST def = (PcodeOpAST) ((VarnodeAST) opAST.getInput(i)).getDef();
				
				if (def == null)
					continue;
				
				VarnodeAST defOut = (VarnodeAST) def.getOutput();
							
				int res = actualLargeValueCheck(def, defOut, var, iter + 1);
				
				if (res == 1)
					return 1;
				else if (res != -1)
					allSafe = false;
			}
			
			if (allSafe)
				return -1;
		}
		
		return 0;
	}
	
	
	private boolean loopAndModified(HighFunction func, PcodeOpAST op, Set<HighVariable> offset) {
		
		return loopAndModified(op, op.getParent(), new LinkedHashSet<PcodeBlockBasic>(), false, offset, func);
	}
	
	
	private boolean loopAndModified(PcodeOpAST op, PcodeBlockBasic block, Set<PcodeBlockBasic> blocks, boolean modified, Set<HighVariable> offset, HighFunction func) {
		
		blocks.add(block);
		
		// if modified in block
		Iterator<PcodeOp> ops = block.getIterator();
		
		while (ops.hasNext()) {
			PcodeOpAST pcop = (PcodeOpAST) ops.next();
			
			if (!pcop.isAssignment())
				continue;
			
			VarnodeAST output = (VarnodeAST) pcop.getOutput();
			
			// If no elements in common
			if (Collections.disjoint(VulnerabilityDetectionUtils.getContainedVars(func, output), offset))
				continue;
		
			modified = true;
			break;
		}		
	
		for (int i = 0; i < block.getOutSize(); i++) {
			
			PcodeBlockBasic out = (PcodeBlockBasic) block.getOut(i);
			
			if (blocks.contains(out)) {
				
				if (out.equals(op.getParent()))
					return modified;
				
				continue;
			}
			
			if (loopAndModified(op, out, blocks, modified, offset, func))
				return true;
			
			blocks.remove(out);
		}
		
		return false;
	}
	
	private Set<HighVariable> getOffset(HighVariable ptr, VarnodeAST vna) {
		
		Set<HighVariable> set = VulnerabilityDetectionUtils.getContainedVars(ptr.getHighFunction(), vna);
		set.remove(ptr);
		return set;
		
	}

	/**
	 * Returns {@code true} if operation is reachable under a given edge and a given reassignment condition, starting from the function entry point.
	 * @param op the operation that is tested for reachability
	 * @param func the function containing the operation. Needed for the edge condition check
	 * @param block the current block. IF CALLING THIS FUNCTION DIRECTLY (AS OPPOSED TO ITS PROXY), PASS IN THE FIRST BASIC BLOCK IN THE FUNCTION
	 * @param var the variable that is tested in the condition checks
	 * @param blocks a list to keep track of already iterated blocks. Needed to prevent endless loops
	 * @param obj an additional object for any further needed items. Is passed to both the edge condition and the reassignment condition. Can be used, for example,
	 * to test multiple variables instead of just var
	 * @param vuln indicates wether the previous block is vulnerable. IF CALLING THIS FUNCTION DIRECTLY (AS OPPOSED TO ITS PROXY), PASS IN {@code true}
	 * @return {@code true} if operation is reachable under a given edge and a given reassignment condition, starting from the function entry point
	 */
	protected boolean reachableIf(PcodeOpAST op, HighFunction func, PcodeBlockBasic block, HighVariable var, Object obj, boolean vuln, HashMap<PcodeBlockBasic, Integer> blocks, HashMap<PcodeBlockBasic, Integer> vulnBlocks) {
		
		int reass = reassCond.check(block, var, obj, op);
				
		if (reass == 1)
			vuln = true;
		else if (reass == -1)
			vuln = false;
		
		if (vuln && block.equals(op.getParent()))
			return true;
		
		if (reass == 10)
			vuln = true;
		else if (reass == -10)
			vuln = false;
		
		boolean vulnOut = false;
		PcodeBlockBasic out = null;
				
		for (int i = 0; i < block.getOutSize(); i++) {
			
			out = (PcodeBlockBasic) block.getOut(i);
			
			if (vuln) {
				vulnBlocks.put(out, vulnBlocks.keySet().contains(out) ? vulnBlocks.get(out) + 1 : 1);
				
				if (vulnBlocks.get(out) > calcDepth)
					continue;
			}
			else {
				blocks.put(out, blocks.keySet().contains(out) ? blocks.get(out) + 1 : 1);
				
				if (blocks.get(out) > calcDepth)
					continue;
			}
				
			if (edgeCond.check(func, block, out, var, obj))
				if (reachableIf(op, func, out, var, obj, vuln, blocks, vulnBlocks)) 
					return true;
		}
		
		return vulnOut;
	}
	
	
	@Override
	public String getString() {
		return "Buffer Overflow";
	}

	@Override
	public String getDescription() {
		return "Execute Buffer Overflow analysis";
	}

}
