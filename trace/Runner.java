/**
 * File: src/trace/Runner.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 1/20/14		hcai		created; for running the event-monitor instrumented code to produce trace
 * 08/18/14		hcai		supported partial tracing now
 *
*/
package trace;

import java.io.*;
import java.lang.reflect.Method;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

import profile.EventMonitor;

public class Runner {
	// the necessary location arguments that give the running subjects */
	/** the subject location and version-seed suffix, with which the class paths, inputs and output dirs are to 
	 * be derived according to the naming routines 
	 */
	protected static String SubjectDir = "";
	protected static String VersionSeed = "";
	/** the entry class name */
	protected static String entryClsName = "";
	/** the class path for the  instrumented subject */
	protected static String BinPath="";
	/** the output path for the  instrumented subject */
	protected static String OutputPath="";
	
	/** the input text that indexes all test cases */
	protected static String testInputFile ="";
	/** the number of tests to execute */
	protected static int	nTests = 0;
	
	/** keep the default output stream */
	private final static PrintStream stdout = System.out;
	private final static PrintStream stderr = System.err;
	
	/** to avoid getting stuck on some test execution, 
	 * we limit the maximal length of time for each, in minutes */
	protected static long MAXTESTDURATION = 30L;
	
	/** map from test to corresponding expected full method trace length */
	protected static Map<String, Integer> test2tracelen = new LinkedHashMap<String, Integer>();
	
	public static void parseArgs(String args[]){
		assert args.length >= 5;
		SubjectDir = args[0];
		VersionSeed = args[1];
		entryClsName = args[2];
		nTests = Integer.valueOf(args[3]);
		System.err.println("Subject: " + SubjectDir + " ver-seed=" + VersionSeed +
				" boostrap class=" + entryClsName + " number of tests=" + nTests);
		
		BinPath = SubjectDir + File.separator + "tracerInstrumented-" + VersionSeed;
		OutputPath = SubjectDir + File.separator + "tracerOutdyn-" + VersionSeed;
				
		testInputFile = SubjectDir + File.separator + "inputs" + File.separator + "testinputs.txt";
		
		if (args.length >= 5) {
			EventMonitor.cachingStates = !args[4].equalsIgnoreCase("-nocaching");
			EventMonitor.stmtExecTimeProfiling = args[4].startsWith("-stmtProf");
		}
		
		if (args.length >= 6) {
			long MaxTestDuration = Long.valueOf(args[5]);
			MAXTESTDURATION = MaxTestDuration;
		}
	}
	
	public static void main(String args[]){
		if (args.length < 4) {
			System.err.println("too few arguments.");
			return;
		}
		parseArgs(args);

		startRunSubject();
		 
		dumpTracelengths(OutputPath + "/traceLengths.txt");
	}
	
	public static void startRunSubject() {	
		String outputDir = OutputPath + File.separator;
		
		File dirF = new File(outputDir);
		if(!dirF.isDirectory())	dirF.mkdirs();
		
		int n = 0;
		BufferedReader br = null;
		
		try {
			FileInputStream fin = null;
			String ts = null;
			fin = new FileInputStream(testInputFile);
			br = new BufferedReader(new InputStreamReader(fin));
			ts = br.readLine();

			while( (ts != null) && n < nTests){
				n++;
				final String[] args = preProcessArg(ts,SubjectDir);
				
				//System.setOut(stdout);
				//System.out.println("test:  " + args[0] + " " + args[1]);
				//////////////////////////////// Run  instrumented subject //////////////////////////////////////////////
				System.setErr(stderr);
				System.err.println("currently at the test No.  " + n);
				final String outputF = outputDir + "test" + n + ".out";
				final String errF = outputDir + "test" + n + ".err";
				
				// redirect stdout and stderr 
				final File outputFile = new File(outputF);
				final PrintStream out = new PrintStream(new FileOutputStream(outputFile)); 
				System.setOut(out); 
				final File errFile = new File(errF);
				final PrintStream err = new PrintStream(new FileOutputStream(errFile)); 
				System.setErr(err);
				
				// set the name of file as the serialization target of method event maps (full trace)
				profile.EventMonitor.setEventSerializeFile(outputDir  + "test"+n+ ".em");
				
				final File runSub = new File(BinPath);
				@SuppressWarnings("deprecation")
				final URL url = runSub.toURL();        
				final URL[] urls = new URL[]{url};
				
			    ExecutorService service = Executors.newSingleThreadExecutor();
			    try {
			        Runnable Runner = new Runnable() {
				@Override public void run() {
								
				try {
					ClassLoader cl = new URLClassLoader( urls, Thread.currentThread().getContextClassLoader() );
					Thread.currentThread().setContextClassLoader(cl);
					    
				    Class<?> cls = cl.loadClass(entryClsName);
				    
				    Method me=cls.getMethod("main", new Class[]{args.getClass()});

				    me.invoke(null, new Object[]{(Object)args});
				}
				catch (Exception e) {
					e.printStackTrace();
				}
				
				out.flush();
				out.close();
				err.flush();
				err.close();
				
				}};
				Future<?>  future = service.submit(Runner);
				future.get(MAXTESTDURATION*60, TimeUnit.SECONDS);
			    }
			    catch (final InterruptedException e) {
			        // The thread was interrupted during sleep, wait or join
			    	System.setErr(stderr);
					System.err.println("Running at the test No.  " + n + " thread interrupted.");
					ts = br.readLine();
					continue;
			    }
			    catch (final TimeoutException e) {
			        // Took too long!
			    	System.setErr(stderr);
					System.err.println("Running at the test No.  " + n + " Time Out after " + MAXTESTDURATION*60 + " seconds");
					
					// for partial tracing 
					profile.EventMonitor.terminate("Enforced by traceRunner.");
					if (profile.EventMonitor.cachingStates) {
						profile.EventMonitor.dumpCachedStates();
					}

					test2tracelen.put("test"+n, profile.EventMonitor.getFullTraceLength());
					ts = br.readLine();
					continue;
			    }
			    catch (final ExecutionException e) {
			        // An exception from within the Runnable task
			    	System.setErr(stderr);
					System.err.println("Running at the test No.  " + n + " exception thrown during test execution + " + e);
					ts = br.readLine();
					continue;
			    }
			    finally {
			        service.shutdown();
					// invoke the "program termination event" for the subject in case there is uncaught exception occurred
					profile.EventMonitor.terminate("Enforced by traceRunner.");
			    }
			    
			    /** save full trace length */
				test2tracelen.put("test"+n, profile.EventMonitor.getFullTraceLength());
				   
				ts = br.readLine();
			}
			
			fin.close();
			br.close();
			
		} catch (Exception e) {
			System.setOut(stdout);
			e.printStackTrace();
		}
		finally {
		}
	}
	
	public static String[] preProcessArg(String arg, String dir) {
		if (arg == null) return null;
		String s1 = arg.replaceAll("\\\\+","/").replaceAll("\\s+", " ");
 
		if(s1.startsWith(" "))
			s1 = s1.substring(1,s1.length());
		String argArray[] =  s1.split(" ");
		for(int i=0;i<argArray.length;i++){
			if(argArray[i].startsWith("..")){
				argArray[i] = argArray[i].replaceFirst("..", dir);
			}
		}		
		return argArray;
	}
	public static void dumpTracelengths(String fn) {
		File fObj = new File(fn);
		try {
			BufferedWriter writer = new BufferedWriter(new FileWriter(fObj));
			
			for (Map.Entry<String, Integer> en : test2tracelen.entrySet()) {
				writer.write(en.getKey() + "\t" + en.getValue() +"\n");
			}
			writer.flush();
			writer.close();
		}
		catch (FileNotFoundException e) { System.err.println("Couldn't write file: " + fObj + e); }
		catch (SecurityException e) { System.err.println("Couldn't write file: " + fObj + e); }
		catch (IOException e) { System.err.println("Couldn't write file: " + fObj + e); }
	}
	
} // Runner

/* vim :set ts=4 tw=4 tws=4 */
