from flask import session

"""
Description:
The DataAnalyticsManager class calculates and retrieves user engagement metrics for the Muscle-Mind application. 
It provides statistics such as the total number of quizzes taken, total questions answered, and the user's 
average score in percentage format. These metrics are designed to enhance the user experience by offering 
insights into progress and performance.

Semi-formal Notation:
/*@ requires A valid DatabaseManager instance (db_manager != null) to execute database queries &&
  @ session['email'] != null (i.e., user is logged in);
  @ ensures Provides accurate user analytics in the form of a dictionary:
  @   - 'quizzes_taken' == COUNT(*) quizzes attempted by the user;
  @   - 'questions_answered' == SUM(questions_answered) by the user;
  @   - 'avg_score' == SUM(score) / SUM(questions_answered) * 100 (percentage, rounded to 2 decimals);
@*/
"""
class DataAnalyticsManager:

    """
    Description:
    Initializes the DataAnalyticsManager instance with a DatabaseManager object. This allows the class to perform 
    database operations required to compute user analytics.

    Semi-formal Notation:
    /*@ requires db_manager != null (valid instance of DatabaseManager);
      @ ensures self.db_manager == db_manager;
    @*/
    """
    def __init__(self, db_manager):
        self.db_manager = db_manager

    """
    Description:
    This method retrieves the analytics data for the currently logged-in user. The method calculates and returns 
    the total number of quizzes taken, total questions answered, and the user's average score in percentage format, 
    rounded to two decimal places.

    Semi-formal Notation:
    /*@ requires session['email'] != null (user is logged in) &&
    @ db_manager.execute_query is functional and correctly retrieves data;
    @ ensures \result == null if session['email'] == null &&
    @ ensures \result == {
    @   'quizzes_taken': SELECT COUNT(*) FROM user_quiz_stats WHERE user_email = session['email'],
    @   'questions_answered': SELECT SUM(questions_answered) FROM user_quiz_stats WHERE user_email = session['email'],
    @   'avg_score': (SUM(score) / SUM(questions_answered)) * 100, rounded to 2 decimal places if SUM(questions_answered) > 0,
    @   'avg_score': 0.0 if SUM(questions_answered) == 0
    @ };
    @*/
    """
    def get_user_analytics(self):
        user_email = session.get('email')
        if not user_email:
            return None
        
        # Query to get the number of quizzes taken, including rows where quiz_id is NULL
        quizzes_taken_query = "SELECT COUNT(*) FROM user_quiz_stats WHERE user_email = %s"
        quizzes_taken = self.db_manager.execute_query(quizzes_taken_query, (user_email,))[0][0]

        # Query to get the total questions answered
        questions_answered_query = "SELECT SUM(questions_answered) FROM user_quiz_stats WHERE user_email = %s"
        questions_answered = self.db_manager.execute_query(questions_answered_query, (user_email,))[0][0] or 0

        # Query to get the total score
        total_score_query = "SELECT SUM(score) FROM user_quiz_stats WHERE user_email = %s"
        total_score = self.db_manager.execute_query(total_score_query, (user_email,))[0][0] or 0

        # Avoid division by zero and calculate the average score as a percentage
        avg_score_percentage = (total_score / questions_answered * 100) if questions_answered > 0 else 0.0

        return {
            'quizzes_taken': quizzes_taken,
            'questions_answered': questions_answered,
            'avg_score': round(avg_score_percentage, 2)  # Rounded to 2 decimal places for percentage display
        }