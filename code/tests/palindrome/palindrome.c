// MiniC program to see if a number is a palindrome

extern int print_int(int X);

bool palindrome(int number) {
   int t;
   int rev;
   int rmndr;
   bool result;

   // print_int(400000);
   // print_int(number);

   rev = 0;   
   result = false;

   t = number;
 
   while (number > 0)
   {
      // print_int(10000000);
      // print_int(number);
      // print_int(rmndr);
      // print_int(rev);
      rmndr = number%10;
      rev = rev*10 + rmndr;
      number = number/10;
      // print_int(20000000);
      // print_int(number);
      // print_int(rmndr);
      // print_int(rev);
   }
   
   if(t == rev) {
      result = true;
   }
   else {
      result = false;
   }
   // print_int(30000000);
   return result;
}