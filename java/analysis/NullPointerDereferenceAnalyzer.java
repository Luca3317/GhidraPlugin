package analysis;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;
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

public class NullPointerDereferenceAnalyzer extends VulnerabilityDetectionAnalyzerComponent {
	
	List<HighVariable> traced;
	
	
	public NullPointerDereferenceAnalyzer() {
		edgeCond = (a, b, c, d, e) -> { return newLeadsToIfNull(a, b, c, d); };
		reassCond = (a, b, c, d) -> { return relevantReassigned(a, b, d); };
	}
		
	@Override
	protected void analyzeFunction(HighFunction func, TaskMonitor monitor, MessageLog log, boolean preferFalseNegatives) throws CancelledException {
					
		
		VulnerabilityDetectionUtils.printBlocks(func);
		
		// Get all dereferencing instructions
		Set<PcodeOpAST> derefs = VulnerabilityDetectionUtils.getDereferencingInstructions(func);
									
		// Get all parameters to later determine wether vulnerability potential or inherent
		Set<HighVariable> params = VulnerabilityDetectionUtils.getParameters(func);
							
		for (PcodeOpAST op : derefs) {
						
			if (op.getInput(1).isConstant() && op.getInput(1).getOffset() == 0) {
				results.addInherent(func.getFunction());
				continue;
			}
			
			List<HighVariable> ptrs = new ArrayList<HighVariable>();
			List<HighVariable> unknowns = new ArrayList<HighVariable>();
			List<HighVariable> nonPtrs = new ArrayList<HighVariable>();
			List<HighVariable> contained = new ArrayList<HighVariable>(VulnerabilityDetectionUtils.getContainedVars(func, (VarnodeAST) op.getInput(1)));
			List<HighVariable> checking;	
			
			if (contained.size() == 0)
				continue;
						
			for (HighVariable var : VulnerabilityDetectionUtils.getContainedVars(func, (VarnodeAST) op.getInput(1))) {
							
				int isPointer = VulnerabilityDetectionUtils.isPointer(var);
						
				if (isPointer == 1)
					ptrs.add(var);
				else if (isPointer == -1)
					unknowns.add(var);
				else
					nonPtrs.add(var);
			}
						
			// if only non pointer contained in dereferenciation
			if (nonPtrs.size() == contained.size()) {
						
				boolean anyChecked = false;
							
				for (HighVariable var : nonPtrs) {
								
					traced = new ArrayList<HighVariable>();
					
					if (!reachableIf(op, func, var, null)) {
						anyChecked = true;
						break;
					}
				}
							
				if (!anyChecked) {
							
					HighVariable rep = nonPtrs.get(0);
								
					if (params.contains(rep))
						results.addPotential(rep);
					else
						results.addInherent(rep);
				}
						
				continue;
			}
						
			checking = new ArrayList<HighVariable>(ptrs);
					
			if (!preferFalseNegatives || ptrs.size() == 0)
				checking.addAll(unknowns);
					
			boolean anyChecked = false;	
				
			for (HighVariable var : checking) {
						
				traced = new ArrayList<HighVariable>();
				
				if (!reachableIf(op, func, var, null)) {
					anyChecked = true;
					break;
				}
			}
						
			if (!anyChecked) {
						
				HighVariable rep = checking.get(0);
						
				if (params.contains(rep))
					results.addPotential(rep);
				else
					results.addInherent(rep);
			}
		}
	}
	
	// Edge condition
	
	private boolean newLeadsToIfNull(HighFunction func, PcodeBlockBasic src, PcodeBlockBasic dest, HighVariable var) {
		
		Iterator<PcodeOp> ops = src.getIterator();
		
		PcodeOp lastPc = null;
		
		// Get last instruction in block
		while (ops.hasNext())	
			lastPc = ops.next();
		
		// If not conditional => true
		if (lastPc.getOpcode() != PcodeOp.CBRANCH)
			return true;
		
		PcodeOp def = lastPc.getInput(1).getDef();
		
		// pointless i think
		if (def == null) {
			Msg.out("\n" + func.getFunction().getName() + " Block " + src.getStart());
			Msg.out("FLAG NOT SET IN SAME BLOCK!!");
			return true;
		}
		
		
		int defOpcode = def.getOpcode();
		
		VarnodeAST input0 = (VarnodeAST) def.getInput(0);
		VarnodeAST input1 = (VarnodeAST) def.getInput(1);
		
		VarnodeAST varNode = null;
		VarnodeAST otherNode = null;
				
		if (Arrays.asList(var.getInstances()).contains(input0)) {
			varNode = input0;
			otherNode = input1;
		}
		if (Arrays.asList(var.getInstances()).contains(input1)) {
			varNode = input1;
			otherNode = input0;
		}
			
		// If var irrelevant
		if (varNode == null)
			return true;
		
		boolean leadsTo = true;
		
		if (lessInstrs.contains(defOpcode)) {
			
			// if var larger than other node
			if (varNode.equals(input1)) {
				
				// constant check
				if (otherNode.isConstant() && otherNode.getOffset() >= 0) {
					if (dest.getStart().equals(src.getTrueOut().getStart()))
						leadsTo = false;
				}
			}
			
			// if other node larger than var
			else {
			
				// constant check
				if (otherNode.isConstant() && otherNode.getOffset() >= 1) {
					if (dest.getStart().equals(src.getFalseOut().getStart()))
						leadsTo = false;
				}
			}
		}
		else if (lessEqualInstrs.contains(defOpcode)) {
			
			// if var larger than other node
			if (varNode.equals(input1)) {
							
				// constant check
				if (otherNode.isConstant() && otherNode.getOffset() >= 1) {
					if (dest.getStart().equals(src.getTrueOut().getStart()))
						leadsTo = false;
				}
			}
						
			// if other node larger than var
			else {
						
				// constant check
				if (otherNode.isConstant() && otherNode.getOffset() >= 0) {
					if (dest.getStart().equals(src.getFalseOut().getStart()))
						leadsTo = false;
				}
			}
		}
		else if (equalInstr.contains(defOpcode)) {
	
			// constant check
			if (otherNode.isConstant() && otherNode.getOffset() == 0) {
				if (dest.getStart().equals(src.getFalseOut().getStart()))
					leadsTo = false;
			}
		}
		else if (notEqualInstr.contains(defOpcode)) {
	
			if (func.getFunction().getName().equals("NPI4"))
				Msg.out("Least im in here if guess");
			
			// constant check
			if (otherNode.isConstant() && otherNode.getOffset() == 0) {
				if (dest.getStart().equals(src.getTrueOut().getStart())) {
					if (func.getFunction().getName().equals("NPI4")) 
						Msg.out("well dayum");
					leadsTo = false;
				}
			}
		}
			
		
		return leadsTo;
	}
		
	//Reassignment condition
	
	protected int relevantReassigned(PcodeBlockBasic block, HighVariable var, PcodeOp pcode) {
								
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
				
				int res = actualValueCheck(opAST, output, var, 0);
				
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

			if (!Arrays.asList(var.getInstances()).contains(output))
				continue;
			
			int res = actualValueCheck(opAST, output, var, 0);
			
			if (res != 0)
				return res;
		}
		
		return changedAfter;
	}
	

	protected int actualValueCheck(PcodeOpAST opAST, VarnodeAST output, HighVariable var, int iter) {
		
		if (iter > calcDepth)
			return 0;
		
		VarnodeAST input0 = (VarnodeAST) opAST.getInput(0);
		VarnodeAST input1 = (VarnodeAST) opAST.getInput(1);
		
		if (opAST.getOpcode() == PcodeOp.COPY) {
						
			// const check
			if (input0.isConstant()) {
				
				if (input0.getOffset() == 0)
					return 1;
				
				return -1;
			}
			
			if (traced.contains(var))
				return 1;
			
			traced.add(var);
			return reachableIf(opAST, var.getHighFunction(), opAST.getInput(0).getHigh(), null) ? 1 : -1;
		}
		else if (addInstrs.contains(opAST.getOpcode())) {
			
			if (input0.isConstant()) {
				
				if (input1.isConstant()) {
					
					if (input0.getOffset() + input1.getOffset() == 0)
						return 1;
					
					return -1;
				}					
			}
		}
		else if (subInstrs.contains(opAST.getOpcode())) {
			
			if (input0.isConstant()) {
				
				if (input1.isConstant()) {
					
					if (input0.getOffset() - input1.getOffset() == 0)
						return 1;
					
					return -1;
				}					
			}
		}
		else if (multInstrs.contains(opAST.getOpcode()) || divInstrs.contains(opAST.getOpcode())) {
			
			if (input0.isConstant()) {
				
				if (input1.isConstant()) {
					
					if (input0.getOffset() * input1.getOffset() == 0)
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
				
				int res = actualValueCheck(def, defOut, var, iter + 1);
				
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
	
	
	@Override
	public String getString() {
		return "Null Pointer Dereference";
	}

	@Override
	public String getDescription() {
		return "Exceute Null Pointer Dereference Analysis";
	}

}
