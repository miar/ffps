import java.util.Map;
import java.util.Collections;
import java.util.HashMap;
import java.util.Hashtable;
import ffpo.*;
import ffps.*;
import com.romix.scala.collection.concurrent.TrieMap;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.ConcurrentSkipListMap;
import java.io.DataInputStream;
import java.io.FileInputStream;

public class MultiThreadInsertLookupRemoveSpeedup {
    
    int [] THREADS;
    int [] DATASETS;
    int RUNS;
    int WARMUP_RUNS;
    int TOTAL_RUNS;  
    int DATASET_SIZE;
    int MAP_SIZE;
    Long DATASET[];
    int LAST_INSERT_I;
    int LAST_LOOKUP_I;
    int LAST_LOOKUP_FOUND_I;
    int LAST_LOOKUP_NFOUND_I;
    
    public Map<Long, Long> CHM = null;
    public ConcurrentSkipListMap <Long, Long> CSLM = null;
    public Map<Long, Long> CT = null;
    public FFPOHashMap <Long, Long> FFPO = null;
    public FFPSHashMap <Long, Long> FFPS = null;  

    public MultiThreadInsertLookupRemoveSpeedup (int threads[], int r, 
						 int  w, int d) {

	THREADS = threads;
	RUNS = r;
	WARMUP_RUNS = w;
	DATASET_SIZE = d;
	DATASET = new Long[DATASET_SIZE];
	TOTAL_RUNS = RUNS + WARMUP_RUNS; 
    }

    /*********************************************************************************
     *    We will be using Concurrent Hash Map to test the correctness of models     *
     *********************************************************************************/

    public void setupRunEnvForDataset(int dataset_id){
	
	/* read the dataset to memory */
	try{
	    FileInputStream fos = new FileInputStream(
 			          "datasets/dataset_" + dataset_id);
	    DataInputStream file_reader = new DataInputStream(fos);
	    
	    for (int i = 0; i < DATASET_SIZE; i++)
		DATASET[i] = file_reader.readLong();
	    file_reader.close();
	} catch (Exception e) {e.printStackTrace();} 
	/* compute the size of the map */
        CHM = new ConcurrentHashMap<Long, Long>();
        for (int i = 0; i < LAST_LOOKUP_FOUND_I; i++)
            CHM.put(DATASET[i], DATASET[i]);
        
        MAP_SIZE = CHM.size();
	System.out.println("Map size = " + MAP_SIZE);
	CHM = null;
	
        return;
    }
    
    /*********************************************************************************
     *                              Concurrent Hash Map                             *
     *********************************************************************************/
    private void chm() throws InterruptedException {
	System.out.println("Map : CHM ");
	for (final int T : THREADS) {	
	    long averageTime = 0;
	    long averageMemory = 0;
	    final int thread_dataset_offset = DATASET_SIZE / T;
	    for (int r = 1; r <= TOTAL_RUNS; r++) {		
		CHM = new ConcurrentHashMap<Long, Long>();		
		/* save a part of the dataset to the remove operation
		   items in this part are all different from the
		   remaining items in the dataset */
		for (int i = LAST_INSERT_I; i < LAST_LOOKUP_FOUND_I; i++) 
		    CHM.put(DATASET[i], DATASET[i]);

		for (int i = LAST_LOOKUP_NFOUND_I; i < DATASET_SIZE; i++) 
		    CHM.put(DATASET[i], DATASET[i]);

		Thread threads[] = new Thread[T];
		for (int t = 0; t < T; t++) {
		    final int tid = t;
		    /* calculate thread_initial_i -> begin */
		    int thread_i = tid * thread_dataset_offset;
		    if (thread_i % T != tid)
			thread_i = thread_i + (T - (thread_i % T)) + tid;    
		    final int thread_initial_i;
		    if (thread_i < DATASET_SIZE)
			thread_initial_i = thread_i;
		    else
			thread_initial_i = tid;
		    /* calculate thread_initial_i -> end */

		    threads[t] = new Thread(new Runnable() {
			    @Override
			    public void run() {
				int i = thread_initial_i;
				if (thread_initial_i < LAST_INSERT_I) { 
				    for (;i < LAST_INSERT_I; i = i + T) 
					CHM.put(DATASET[i], DATASET[i]);  		    
				    for (; i < LAST_LOOKUP_I; i = i + T)
					CHM.get(DATASET[i]);				    
				    for (; i < DATASET_SIZE; i = i + T) 
					CHM.remove(DATASET[i]);				    
				    for (i = tid; i < thread_initial_i; i = i + T) 
					CHM.put(DATASET[i], DATASET[i]); 
				} else if (thread_initial_i < LAST_LOOKUP_I) { 
				    for (; i < LAST_LOOKUP_I; i = i + T)
					CHM.get(DATASET[i]);			        
				    for (; i < DATASET_SIZE; i = i + T)
					CHM.remove(DATASET[i]);			    
				    for (i = tid; i < LAST_INSERT_I; i = i + T) 
					CHM.put(DATASET[i], DATASET[i]);
				    for (; i < thread_initial_i; i = i + T)
					CHM.get(DATASET[i]);
				} else {
				    for (; i < DATASET_SIZE; i = i + T) 
					CHM.remove(DATASET[i]);
				    for (i = tid; i < LAST_INSERT_I; i = i + T) 
					CHM.put(DATASET[i], DATASET[i]);		    
				    for (; i < LAST_LOOKUP_I; i = i + T)
					CHM.get(DATASET[i]);				    
				    for (; i < thread_initial_i; i = i + T) 
					CHM.remove(DATASET[i]);
				}
			    }
			});
		}
		long time = System.nanoTime();
		for (int t = 0; t < T; t++)
		    threads[t].start();
		for (int t = 0; t < T; t++)
		    threads[t].join();

		long timeUsed = (System.nanoTime() - time) / 1000000L;
		if (r > WARMUP_RUNS) {
		    averageTime += timeUsed;
		    averageMemory += Runtime.getRuntime().totalMemory() - 
			             Runtime.getRuntime().freeMemory();
		}
		//if (MAP_SIZE != CHM.size())
		//    System.out.println("ERROR IN MAP SIZE -> "+ MAP_SIZE + " " + CHM.size());
		CHM = null;
	    }
	    System.out.println("Threads = " + T + " Time = " + 
			       averageTime / RUNS + " MSeconds" + 
			       " Memory = " + averageMemory / RUNS / 1024 / 1024 + " MBytes");
	}
	return;
    }

    /*********************************************************************************
     *                              Concurrent Skip Lists                            *
     *********************************************************************************/
    private void cslm() throws InterruptedException {
	System.out.println("Map : CSLM ");
	for (final int T : THREADS) {	
	    long averageTime = 0;	    
	    long averageMemory = 0;
	    final int thread_dataset_offset = DATASET_SIZE / T;
	    for (int r = 1; r <= TOTAL_RUNS; r++) {		
		CSLM = new ConcurrentSkipListMap<Long, Long>();
		/* save a part of the dataset to the remove operation
		   items in this part are all different from the remaining items
		   in the dataset */
		for (int i = LAST_INSERT_I; i < LAST_LOOKUP_FOUND_I; i++) 
		    CSLM.put(DATASET[i], DATASET[i]);

		for (int i = LAST_LOOKUP_NFOUND_I; i < DATASET_SIZE; i++) 
		    CSLM.put(DATASET[i], DATASET[i]);

		Thread threads[] = new Thread[T];
		for (int t = 0; t < T; t++) {
		    final int tid = t;
		    /* calculate thread_initial_i -> begin */
		    int thread_i = tid * thread_dataset_offset;
		    if (thread_i % T != tid)
			thread_i = thread_i + (T - (thread_i % T)) + tid; 
		    final int thread_initial_i;
		    if (thread_i < DATASET_SIZE)
			thread_initial_i = thread_i;
		    else
			thread_initial_i = tid;
		    /* calculate thread_initial_i -> end */

		    threads[t] = new Thread(new Runnable() {
			    @Override
			    public void run() {					
				int i = thread_initial_i;
				if (thread_initial_i < LAST_INSERT_I) { 
				    for (;i < LAST_INSERT_I; i = i + T) 
					CSLM.put(DATASET[i], DATASET[i]);		    
				    for (; i < LAST_LOOKUP_I; i = i + T)
					CSLM.get(DATASET[i]);				    
				    for (; i < DATASET_SIZE; i = i + T) 
					CSLM.remove(DATASET[i]);			    
				    for (i = tid; i < thread_initial_i; i = i + T) 
					CSLM.put(DATASET[i], DATASET[i]);
				} else if (thread_initial_i < LAST_LOOKUP_I) { 
				    for (; i < LAST_LOOKUP_I; i = i + T)
					CSLM.get(DATASET[i]);				    
				    for (; i < DATASET_SIZE; i = i + T) 
					CSLM.remove(DATASET[i]);		    
				    for (i = tid; i < LAST_INSERT_I; i = i + T) 
					CSLM.put(DATASET[i], DATASET[i]);	    
				    for (; i < thread_initial_i; i = i + T)
					CSLM.get(DATASET[i]);
				} else {
				    for (; i < DATASET_SIZE; i = i + T) 
					CSLM.remove(DATASET[i]);
				    for (i = tid; i < LAST_INSERT_I; i = i + T) 
					CSLM.put(DATASET[i], DATASET[i]);		    
				    for (; i < LAST_LOOKUP_I; i = i + T)
					CSLM.get(DATASET[i]);				    
				    for (; i < thread_initial_i; i = i + T) 
					CSLM.remove(DATASET[i]);
				}
			    }
			});
		}
		long time = System.nanoTime();		
		for (int t = 0; t < T; t++)
		    threads[t].start();
		for (int t = 0; t < T; t++)
		    threads[t].join();
		long timeUsed = (System.nanoTime() - time) / 1000000L;
		if (r > WARMUP_RUNS) {
		    averageTime += timeUsed;
		    averageMemory += Runtime.getRuntime().totalMemory() - 
 			             Runtime.getRuntime().freeMemory();
		}
		// if(MAP_SIZE != CSLM.size()) {
		//     System.out.println("ERROR IN MAP SIZE -> "+ MAP_SIZE + " " + CSLM.size());
		// }		
		CSLM = null;
	    }
	    System.out.println("Threads = " + T + " Time = " + 
			       averageTime / RUNS + " MSeconds" +
			       " Memory = " + averageMemory / RUNS / 1024 / 1024 + " MBytes");
	}
	return;
    }


    /*********************************************************************************
     *                              Concurrent Tries                                 *
     *********************************************************************************/

    private void ct() throws InterruptedException {
	System.out.println("Map : CT ");

	for (final int T : THREADS) {	
	    long averageTime = 0;
	    long averageMemory = 0;
	    final int thread_dataset_offset = DATASET_SIZE / T;
	    for (int r = 1; r <= TOTAL_RUNS; r++) {		
		CT = new TrieMap<Long, Long>();
		/* save a part of the dataset to the remove operation
		   items in this part are all different from the remaining items
		   in the dataset */
		for (int i = LAST_INSERT_I; i < LAST_LOOKUP_FOUND_I; i++) 
		    CT.put(DATASET[i], DATASET[i]);
		for (int i = LAST_LOOKUP_NFOUND_I; i < DATASET_SIZE; i++) 
		    CT.put(DATASET[i], DATASET[i]);
		Thread threads[] = new Thread[T];
		for (int t = 0; t < T; t++) {
		    final int tid = t;
		    /* calculate thread_initial_i -> begin */
		    int thread_i = tid * thread_dataset_offset;
		    if (thread_i % T != tid)
			thread_i = thread_i + (T - (thread_i % T)) + tid;    
		    final int thread_initial_i;
		    if (thread_i < DATASET_SIZE)
			thread_initial_i = thread_i;
		    else
			thread_initial_i = tid;
		    /* calculate thread_initial_i -> end */

		    threads[t] = new Thread(new Runnable() {
			    @Override
			    public void run() {					
				int i = thread_initial_i;
				if (thread_initial_i < LAST_INSERT_I) { 
				    for (;i < LAST_INSERT_I; i = i + T) 
					CT.put(DATASET[i], DATASET[i]);			    
				    for (; i < LAST_LOOKUP_I; i = i + T)
					CT.get(DATASET[i]);				    
				    for (; i < DATASET_SIZE; i = i + T) 
					CT.remove(DATASET[i]);				    
				    for (i = tid; i < thread_initial_i; i = i + T) 
					CT.put(DATASET[i], DATASET[i]);		
				} else if (thread_initial_i < LAST_LOOKUP_I) { 
				    for (; i < LAST_LOOKUP_I; i = i + T)
					CT.get(DATASET[i]);				    
				    for (; i < DATASET_SIZE; i = i + T) 
					CT.remove(DATASET[i]);				    
				    for (i = tid; i < LAST_INSERT_I; i = i + T) 
					CT.put(DATASET[i], DATASET[i]);		    
				    for (; i < thread_initial_i; i = i + T)
					CT.get(DATASET[i]);
				} else {
				    for (; i < DATASET_SIZE; i = i + T) 
					CT.remove(DATASET[i]);
				    for (i = tid; i < LAST_INSERT_I; i = i + T) 
					CT.put(DATASET[i], DATASET[i]);		    
				    for (; i < LAST_LOOKUP_I; i = i + T)
					CT.get(DATASET[i]);				    
				    for (; i < thread_initial_i; i = i + T) 
					CT.remove(DATASET[i]);
				}
			    }
			});
		}
		long time = System.nanoTime();
		for (int t = 0; t < T; t++)
		    threads[t].start();
		for (int t = 0; t < T; t++)
		    threads[t].join();
		long timeUsed = (System.nanoTime() - time) / 1000000L;
		if (r > WARMUP_RUNS) {
		    averageTime += timeUsed;
		    averageMemory += Runtime.getRuntime().totalMemory() - 
			Runtime.getRuntime().freeMemory();				    
		}
		// if(MAP_SIZE != CT.size()) {
		//     System.out.println("ERROR IN MAP SIZE -> "+ MAP_SIZE + " " + CT.size());
		//     //System.exit(0);
		// }
		
		CT = null;
	    }
	    System.out.println("Threads = " + T + " Time = " + 
			       averageTime / RUNS + " MSeconds" +
			       " Memory = " + averageMemory / RUNS / 1024 / 1024 + " MBytes");
	}
	return;
    }


    /*********************************************************************************
     *                             FFPO Hash Map                                     *
     *********************************************************************************/
    private void ffpo(int hashSize) throws InterruptedException {
	System.out.println("Map : FFPO");

	for (final int T : THREADS) {	
	    long averageTime = 0;
	    long averageMemory = 0;
	    final int thread_dataset_offset = DATASET_SIZE / T;
	    for (int r = 1; r <= TOTAL_RUNS; r++) {		
		FFPO = new FFPOHashMap<Long, Long>(hashSize);
		/* save a part of the dataset to the remove operation
		   items in this part are all different from the remaining items
		   in the dataset */
		for (int i = LAST_INSERT_I; i < LAST_LOOKUP_FOUND_I; i++) 
		    FFPO.put(DATASET[i], DATASET[i]);
		for (int i = LAST_LOOKUP_NFOUND_I; i < DATASET_SIZE; i++) 
		    FFPO.put(DATASET[i], DATASET[i]);
		Thread threads[] = new Thread[T];
		for (int t = 0; t < T; t++) {
		    final int tid = t;
		    /* calculate thread_initial_i -> begin */
		    int thread_i = tid * thread_dataset_offset;
		    if (thread_i % T != tid)
			thread_i = thread_i + (T - (thread_i % T)) + tid;    
		    final int thread_initial_i;
		    if (thread_i < DATASET_SIZE)
			thread_initial_i = thread_i;
		    else
			thread_initial_i = tid;
		    /* calculate thread_initial_i -> end */
		    threads[t] = new Thread(new Runnable() {
			    @Override
			    public void run() {
				int i = thread_initial_i;
				if (thread_initial_i < LAST_INSERT_I) { 
				    for (;i < LAST_INSERT_I; i = i + T) 
					FFPO.put(DATASET[i], DATASET[i]);		    
				    for (; i < LAST_LOOKUP_I; i = i + T)
					FFPO.get(DATASET[i]);				    
				    for (; i < DATASET_SIZE; i = i + T) 
					FFPO.remove(DATASET[i]);				    
				    for (i = tid; i < thread_initial_i; i = i + T) 
					FFPO.put(DATASET[i], DATASET[i]);
				} else if (thread_initial_i < LAST_LOOKUP_I) { 
				    for (; i < LAST_LOOKUP_I; i = i + T)
					FFPO.get(DATASET[i]);			    
				    for (; i < DATASET_SIZE; i = i + T) 
					FFPO.remove(DATASET[i]);				    
				    for (i = tid; i < LAST_INSERT_I; i = i + T) 
					FFPO.put(DATASET[i], DATASET[i]);	    
				    for (; i < thread_initial_i; i = i + T)
					FFPO.get(DATASET[i]);
				} else {
				    for (; i < DATASET_SIZE; i = i + T) 
					FFPO.remove(DATASET[i]);
				    for (i = tid; i < LAST_INSERT_I; i = i + T) 
					FFPO.put(DATASET[i], DATASET[i]); 		    
				    for (; i < LAST_LOOKUP_I; i = i + T)
					FFPO.get(DATASET[i]);				    
				    for (; i < thread_initial_i; i = i + T) 
					FFPO.remove(DATASET[i]);
				}				
			    }
			});
		}

		long time = System.nanoTime();

		for (int t = 0; t < T; t++)
		    threads[t].start();

		for (int t = 0; t < T; t++)
		    threads[t].join();

		long timeUsed = (System.nanoTime() - time) / 1000000L;
		if (r > WARMUP_RUNS) {
		    averageTime += timeUsed;
		    averageMemory += Runtime.getRuntime().totalMemory() - 
			             Runtime.getRuntime().freeMemory();
		}		    

		//if(MAP_SIZE != FFPO.size()) {
		// System.out.println("ERROR IN MAP SIZE -> "+ MAP_SIZE + " " + FFPO.size());
		   //System.exit(0);
		//}
		//FFPO.flush_hash_statistics(false);

		FFPO = null;
	    }
	    
	    System.out.println("Threads = " + T + " Time = " + 
			       averageTime / RUNS + " MSeconds" +
			       " Memory = " + averageMemory / RUNS / 1024 / 1024 + " MBytes");
	}
	return;
    }


    /*********************************************************************************
     *                             FFPS Hash Map                                     *
     *********************************************************************************/
    private void ffps(int hashSize) throws InterruptedException {
	System.out.println("Map : FFPS");

	for (final int T : THREADS) {	
	    long averageTime = 0;
	    long averageMemory = 0;
	    final int thread_dataset_offset = DATASET_SIZE / T;
	    for (int r = 1; r <= TOTAL_RUNS; r++) {		
		FFPS = new FFPSHashMap<Long, Long>(hashSize);
		/* save a part of the dataset to the remove operation
		   items in this part are all different from the remaining items
		   in the dataset */
		for (int i = LAST_INSERT_I; i < LAST_LOOKUP_FOUND_I; i++) 
		    FFPS.put(DATASET[i], DATASET[i]);
		for (int i = LAST_LOOKUP_NFOUND_I; i < DATASET_SIZE; i++) 
		    FFPS.put(DATASET[i], DATASET[i]);
		Thread threads[] = new Thread[T];
		for (int t = 0; t < T; t++) {
		    final int tid = t;
		    /* calculate thread_initial_i -> begin */
		    int thread_i = tid * thread_dataset_offset;
		    if (thread_i % T != tid)
			thread_i = thread_i + (T - (thread_i % T)) + tid;    
		    final int thread_initial_i;
		    if (thread_i < DATASET_SIZE)
			thread_initial_i = thread_i;
		    else
			thread_initial_i = tid;
		    /* calculate thread_initial_i -> end */
		    threads[t] = new Thread(new Runnable() {
			    @Override
			    public void run() {
				int i = thread_initial_i;
				if (thread_initial_i < LAST_INSERT_I) { 
				    for (;i < LAST_INSERT_I; i = i + T) 
					FFPS.put(DATASET[i], DATASET[i]);		    
				    for (; i < LAST_LOOKUP_I; i = i + T)
					FFPS.get(DATASET[i]);				    
				    for (; i < DATASET_SIZE; i = i + T) 
					FFPS.remove(DATASET[i]);				    
				    for (i = tid; i < thread_initial_i; i = i + T) 
					FFPS.put(DATASET[i], DATASET[i]);
				} else if (thread_initial_i < LAST_LOOKUP_I) { 
				    for (; i < LAST_LOOKUP_I; i = i + T)
					FFPS.get(DATASET[i]);			    
				    for (; i < DATASET_SIZE; i = i + T) 
					FFPS.remove(DATASET[i]);				    
				    for (i = tid; i < LAST_INSERT_I; i = i + T) 
					FFPS.put(DATASET[i], DATASET[i]);	    
				    for (; i < thread_initial_i; i = i + T)
					FFPS.get(DATASET[i]);
				} else {
				    for (; i < DATASET_SIZE; i = i + T) 
					FFPS.remove(DATASET[i]);
				    for (i = tid; i < LAST_INSERT_I; i = i + T) 
					FFPS.put(DATASET[i], DATASET[i]); 		    
				    for (; i < LAST_LOOKUP_I; i = i + T)
					FFPS.get(DATASET[i]);				    
				    for (; i < thread_initial_i; i = i + T) 
					FFPS.remove(DATASET[i]);
				}				
			    }
			});
		}

		long time = System.nanoTime();

		for (int t = 0; t < T; t++)
		    threads[t].start();

		for (int t = 0; t < T; t++)
		    threads[t].join();

		long timeUsed = (System.nanoTime() - time) / 1000000L;
		if (r > WARMUP_RUNS) {
		    averageTime += timeUsed;
		    averageMemory += Runtime.getRuntime().totalMemory() - 
			             Runtime.getRuntime().freeMemory();
		}		    

		//if(MAP_SIZE != FFPS.size()) {
		// System.out.println("ERROR IN MAP SIZE -> "+ MAP_SIZE + " " + FFPS.size());
		   //System.exit(0);
		//}
		//FFPS.flush_hash_statistics(false);

		FFPS = null;
	    }
	    
	    System.out.println("Threads = " + T + " Time = " + 
			       averageTime / RUNS + " MSeconds" +
			       " Memory = " + averageMemory / RUNS / 1024 / 1024 + " MBytes");
	}
	return;
    }



    
    public void run(int di, int last_insert_i, int last_lookup_found_i,  int last_lookup_nfound_i,
		    boolean chm, boolean cslm, boolean ct, boolean ffpo, boolean ffps) 
	throws InterruptedException {
	
	LAST_INSERT_I = last_insert_i;
	LAST_LOOKUP_FOUND_I = last_lookup_found_i;
	LAST_LOOKUP_NFOUND_I = last_lookup_nfound_i;
	LAST_LOOKUP_I = LAST_LOOKUP_NFOUND_I;
	setupRunEnvForDataset(di);	    
	if (chm)
	    chm();	
	if (cslm)
	    cslm();
	if (ct)
	    ct();
	if (ffpo)
	    ffpo(4);
	if (ffps)
	    ffps(4);
	return;
    }
}

