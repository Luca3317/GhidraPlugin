package analysis;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import ghidra.app.util.importer.MessageLog;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.FunctionIterator;
import ghidra.program.model.listing.FunctionManager;
import ghidra.program.model.listing.Program;
import ghidra.program.model.pcode.HighFunction;
import ghidra.util.Msg;
import ghidra.util.exception.CancelledException;
import ghidra.util.task.TaskMonitor;

public class UnsafeLibraryFunctionDetection extends VulnerabilityDetectionAnalyzerComponent {

	private Set<String> inhFuncSigns = null;
	private Set<String> potFuncSigns = null;
		
	private void createFiles() throws IOException {
		String basePath = System.getProperty("user.dir");
		String path = basePath + "\\Extensions\\Ghidra\\inherent.txt";
		File f = new File(path);
		if(!f.exists() || f.isDirectory()) { 
		   
			List<String> lines = Arrays.asList("gets");
			PrintWriter writer = new PrintWriter(path, "UTF-8");
			
			for (int i = 0; i < lines.size(); i++)
				writer.println(lines.get(i));
			
			writer.close();
		}
		
		path = basePath + "\\Extensions\\Ghidra\\potential.txt";
		f = new File(path);
		if(!f.exists() || f.isDirectory()) { 
		   
			List<String> lines = Arrays.asList("printf", "fprintf", "sprintf", "snprintf", "strlen", "memset", "memcpy", "strcpy", "memmove", "atoi", "strdup", "calloc", "strchr");
			PrintWriter writer = new PrintWriter(path, "UTF-8");
			
			for (int i = 0; i < lines.size(); i++)
				writer.println(lines.get(i));
			
			writer.close();
		}
	}
	
	public void analyze(Program program, TaskMonitor monitor, MessageLog log, boolean preferFalseNegatives) throws CancelledException {
			
		try {
			createFiles();
		} catch (Exception e) {
			log.appendMsg("failed creation: " + e.getMessage());
		}
		
		results = new VulnerabilityDetectionResults(getString());
		
		try {
			init();
		}
		catch(Exception e) {
			log.appendMsg("failed other " + e.getMessage());
			return;
		}
		
		FunctionManager funMan = program.getFunctionManager();
		FunctionIterator fIter = funMan.getExternalFunctions();
		
	
		Msg.out("\n\n");
		while (fIter.hasNext()) {
			Function func = fIter.next();
			
			if (inhFuncSigns.contains(func.getName()))
				results.addInherent(func);
			else if (potFuncSigns.contains(func.getName()))
				results.addPotential(func);
			
		}
	}
	
	@Override
	protected void analyzeFunction(HighFunction func, TaskMonitor monitor, MessageLog log, boolean preferFalseNegatives) throws CancelledException {	}
	
	private void init() throws FileNotFoundException, IOException {
		
		String basePath = System.getProperty("user.dir");
		String path = basePath + "\\Extensions\\Ghidra\\inherent.txt";
		
		inhFuncSigns = new HashSet<String>();
		
		BufferedReader br = new BufferedReader(new FileReader(path));
		try {
		    String line = br.readLine();

		    while (line != null) {
		       
		    	inhFuncSigns.add(line);
		        line = br.readLine();
		    }
		
		} catch(Exception e) {			
			throw e;
		} finally {
		    br.close();
		}
		
		
		path = basePath + "\\Extensions\\Ghidra\\potential.txt";
		
		potFuncSigns = new HashSet<String>();

		br = new BufferedReader(new FileReader(path));
		try {
		    String line = br.readLine();

		    while (line != null) {
		       
		    	potFuncSigns.add(line);
		        line = br.readLine();
		    }
		
		} catch(Exception e) {			
			throw e;
		} finally {
		    br.close();
		}	
	}
	
	@Override
	public String getString() {
		return "Unsafe Library Function Detection";
	}

	@Override
	public String getDescription() {
		return "Detect Unsafe Library Functions";
	}
}
