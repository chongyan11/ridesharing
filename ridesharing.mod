/*********************************************
 * OPL 12.7.0.0 Model
 * Author: mailc
 * Creation Date: 20 Sep, 2017 at 8:49:20 pm
 *********************************************/
 
 tuple Coordinate {
 	int x;
 	int y; 
 }
 tuple ODPair {
 	Coordinate origin;
 	Coordinate destination; 
 }
 tuple TimePair {
 	int earlyTime;
 	int lateTime; 
 }
 tuple TripAnnouncement {
 	key int sn;
 	int type;
 	TimePair time;
 	ODPair od;
 }
 float speed = 1;
 int nA = ...;
 
 // Reads all trip announcements and splits them according to driver, rider types 
 {TripAnnouncement} Announcements = ...;
 {TripAnnouncement} DriverAnnouncements = {i | i in Announcements: i.type == 1};
 {TripAnnouncement} RiderAnnouncements = {i | i in Announcements: i.type == 2};
 
 int nDrivers = card(DriverAnnouncements);
 int nRiders = card(RiderAnnouncements);
  
 range drivers = 0..nDrivers-1;
 range riders = 0..nRiders-1;
 
 //distances between o(d)-o(r), o(r)-d(r), d(r)-d(d), o(d)-d(d)
 float oo[drivers][riders];
 float dd[drivers][riders];
 float odriders[riders];
 float oddrivers[drivers];
 // computes straight line distances based on coordinates given, item(set, i) retrieves ith item in set, pow(float, float) raises power
 execute {
 	for(var i in drivers) {
 		for (var j in riders) {
 			oo[i][j] = Opl.sqrt(Opl.pow((Opl.item(DriverAnnouncements, i).od.origin.x - Opl.item(RiderAnnouncements, j).od.origin.x), 2) + 
 				Opl.pow((Opl.item(DriverAnnouncements, i).od.origin.y - Opl.item(RiderAnnouncements, j).od.origin.y), 2));
 			dd[i][j] = Opl.sqrt(Opl.pow((Opl.item(DriverAnnouncements, i).od.destination.x - Opl.item(RiderAnnouncements, j).od.destination.x), 2) + 
 				Opl.pow((Opl.item(DriverAnnouncements, i).od.destination.y - Opl.item(RiderAnnouncements, j).od.destination.y), 2));
 			odriders[j] = Opl.sqrt(Opl.pow((Opl.item(RiderAnnouncements, j).od.origin.x - Opl.item(RiderAnnouncements, j).od.destination.x), 2) + 
 				Opl.pow((Opl.item(RiderAnnouncements, j).od.origin.y - Opl.item(RiderAnnouncements, j).od.destination.y), 2));		
		}
 		oddrivers[i] = Opl.sqrt(Opl.pow((Opl.item(DriverAnnouncements, i).od.origin.x - Opl.item(DriverAnnouncements, i).od.destination.x), 2) + 
 				Opl.pow((Opl.item(DriverAnnouncements, i).od.origin.y - Opl.item(DriverAnnouncements, i).od.destination.y), 2)); 	
 	}
 }
 
 dvar int+ x[drivers][riders];
 dvar int+ y[drivers];
 dvar int+ w[riders];
 dvar float+ departTime[drivers];
 
 float c[drivers][riders];	// cost matrix (given sharing) which is the sum of distances if rides are shared
 float todor[drivers][riders];	// time matrix for origin driver to origin rider (assumed fixed speed, can explore option of giving each driver a speed which follows certain distributions) 
 float tordr[drivers][riders];	// time matrix for origin rider to destination rider
 float tdrdd[drivers][riders];	// time matrix for destination rider to destination driver
 float driverEarliestDepartTime[drivers];
 float driverLatestArrivalTime[drivers];
 float riderEarliestDepartTime[riders];
 float riderLatestArrivalTime[riders];
 
 // Construct distance matrix (which represents cost in this simple application) and time matrices (for constraining later on)
 execute {
 	for(var i in drivers) {
 		for(var j in riders) {
 		 	c[i][j] = oo[i][j] + dd[i][j] + odriders[j];
 		 	todor[i][j] = oo[i][j]/speed;
 		 	tordr[i][j] = odriders[j]/speed;
 		 	tdrdd[i][j] = dd[i][j]/speed;
 		 	riderEarliestDepartTime[j] = Opl.item(RiderAnnouncements, j).time.earlyTime;
 		 	riderLatestArrivalTime[j] = Opl.item(RiderAnnouncements, j).time.lateTime;	
 		} 
 		driverEarliestDepartTime[i] = Opl.item(DriverAnnouncements, i).time.earlyTime;
 		driverLatestArrivalTime[i] = Opl.item(DriverAnnouncements, i).time.lateTime;
 	} 		
 }
 
 minimize 
 	sum (i in drivers, j in riders) (c[i][j]*x[i][j]) + 
 	sum (i in drivers) (oddrivers[i]*y[i]) + 
 	sum (j in riders) (odriders[j]*w[j]) ;
 		
 subject to {
 	forall (i in drivers, j in riders) {
 	  ctTime1:
 	  	departTime[i] >= driverEarliestDepartTime[i];
 	  ctTime2:	
 	  	departTime[i] + todor[i][j] >= riderEarliestDepartTime[j];
 	  ctTime3:	
 	  	departTime[i] + todor[i][j] + tordr[i][j] <= riderLatestArrivalTime[j];
 	  ctTime4:	
 	  	departTime[i] + todor[i][j] + tordr[i][j] + tdrdd[i][j] <= driverLatestArrivalTime[i];
   }
   	forall (j in riders) {
   	  ctRiders1:
   	  	sum (i in drivers) (x[i][j] + w[j]) == 1;	
   }
   	forall (i in drivers) {
   	  ctDrivers1:
   	  	sum (j in riders) (x[i][j] + y[i]) == 1;
   }
   ctTotalDrivers:
   		sum (i in drivers, j in riders) (x[i][j] + y[i]) == nDrivers;
   ctTotalRiders:
   		sum (i in drivers, j in riders) (x[i][j] + w[j]) == nRiders;
 }
 
 float worstCase = sum (i in drivers) oddrivers[i] + sum (j in riders) odriders[j];
 
 execute {
 	writeln(cplex.getObjValue()); 
 	writeln(worstCase);
 	writeln(worstCase - cplex.getObjValue());
 }
 
 
 