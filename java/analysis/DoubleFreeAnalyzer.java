package analysis;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Set;

import ghidra.app.util.importer.MessageLog;
import ghidra.program.model.listing.FunctionIterator;
import ghidra.program.model.listing.FunctionManager;
import ghidra.program.model.listing.FunctionSignature;
import ghidra.program.model.listing.Program;
import ghidra.program.model.pcode.HighFunction;
import ghidra.program.model.pcode.HighVariable;
import ghidra.program.model.pcode.PcodeBlockBasic;
import ghidra.program.model.pcode.PcodeOp;
import ghidra.program.model.pcode.PcodeOpAST;
import ghidra.program.model.pcode.Varnode;
import ghidra.program.model.pcode.VarnodeAST;
import ghidra.util.exception.CancelledException;
import ghidra.util.task.TaskMonitor;

public class DoubleFreeAnalyzer extends VulnerabilityDetectionAnalyzerComponent {

	private FunctionManager funcMan;
	private List<FunctionSignature> extFuncs;
	
	@Override
	public void analyze(Program program, TaskMonitor monitor, MessageLog log, boolean preferFalseNegatives) throws CancelledException {
				
		funcMan = program.getFunctionManager();
		extFuncs = new ArrayList<FunctionSignature>();
		
		FunctionIterator fit = funcMan.getExternalFunctions();
		while (fit.hasNext()) {
			extFuncs.add(fit.next().getSignature());
		}
		
		Set<HighFunction> hFuncs = VulnerabilityDetectionUtils.getHighFunctions(monitor, log);
		results = new VulnerabilityDetectionResults(getString());
		
		for (HighFunction highFunction : hFuncs)
			analyzeFunction(highFunction, monitor, log, preferFalseNegatives);		
	}
	
	
	@Override
	protected void analyzeFunction(HighFunction func, TaskMonitor monitor, MessageLog log, boolean preferFalseNegatives) throws CancelledException {

		List<PcodeOpAST> allOps = VulnerabilityDetectionUtils.getInstructions(func);
		List<PcodeOpAST> freeOps = VulnerabilityDetectionUtils.getInstructions(func);
		freeOps = VulnerabilityDetectionUtils.filterPcodeInstructions(freeOps, Arrays.asList(PcodeOp.CALL));
		
		for (PcodeOpAST op : new ArrayList<PcodeOpAST>(freeOps)) {
				
			if (!funcMan.getReferencedFunction(((VarnodeAST) op.getInput(0)).getAddress()).getName().equals("free") || !extFuncs.contains(funcMan.getReferencedFunction(((VarnodeAST) op.getInput(0)).getAddress()).getSignature())) 
				freeOps.remove(op);
		}
		
		Set<HighVariable> vars = VulnerabilityDetectionUtils.getLocalVariables(func);
		vars.addAll(VulnerabilityDetectionUtils.getParameters(func));
		
		for (HighVariable var : vars) {
			
			List<PcodeOpAST> relOps = new ArrayList<PcodeOpAST>();
			List<Varnode> varInstances = Arrays.asList(var.getInstances());
			
			for (PcodeOpAST op : freeOps) {
				
				if (varInstances.contains(op.getInput(1)))
					relOps.add(op);
			}
			
			List<PcodeOpAST> relReassOps = new ArrayList<PcodeOpAST>();
			for (PcodeOpAST op : allOps) {
				
				if (!op.isAssignment())
					continue;
				
				if (varInstances.contains(op.getOutput()))
					relReassOps.add(op);
			}
			
			if (freeAfterFreeCheck(func.getBasicBlocks().get(0), relOps, relReassOps, new HashMap<PcodeBlockBasic, Integer>(), 0)) {
				results.addInherent(var);
				break;
			}
		}
	}
	
	
	
	private boolean freeAfterFreeCheck(PcodeBlockBasic block, List<PcodeOpAST> freeOps, List<PcodeOpAST> reassOps, HashMap<PcodeBlockBasic, Integer> visited, int amount) {
		
		List<PcodeOp> ops = new ArrayList<PcodeOp>();
		block.getIterator().forEachRemaining(ops::add);
		for (PcodeOp op : ops) {
			
			if (freeOps.contains(op))
				amount++;
			else if (reassOps.contains(op))
				amount = 0;
			
			if (amount > 1)
				return true;
		}
				
		PcodeBlockBasic out = null;
		for (int i = 0; i < block.getOutSize(); i++) {
			
			out = (PcodeBlockBasic) block.getOut(i);
			
			visited.put(out, visited.keySet().contains(out) ? visited.get(out) + 1 : 1);
			
			if (visited.get(out) > calcDepth)
				continue;			
						
			if (freeAfterFreeCheck(out, freeOps, reassOps, visited, amount))
					return true;
		}
		
		return false;
	}
	
	
	@Override
	public String getString() {
		return "Double Free";
	}

	@Override
	public String getDescription() {
		return "Execute Double Free analysis";
	}

}
