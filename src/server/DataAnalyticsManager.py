from flask import session

"""
The DataAnalyticsManager class calculates and retrieves user engagement metrics for the Muscle-Mind application. 
It provides analytics such as the total number of quizzes taken, the total number of questions answered, and 
the user's average score as a percentage. This data offers users insight into their performance and activity 
within the platform, enhancing their experience by making progress visible.

@requires:
- A valid DatabaseManager instance to execute queries.
- The user's email to be stored in the session object to identify the user.

@ensures:
- Provides accurate user analytics, with results returned as a dictionary containing:
    - 'quizzes_taken': int - Total number of distinct quizzes taken by the user.
    - 'questions_answered': int - Total number of questions answered by the user across all quizzes.
    - 'avg_score': float - Average score in percentage format, rounded to two decimal places.
"""
class DataAnalyticsManager:
    """
    The DataAnalyticsManager class is responsible for calculating user analytics, such as
    the number of quizzes taken, total questions answered, and average score for each user.
    It interacts with the database through DatabaseManager to retrieve and compute statistics.
    
    @requires A valid DatabaseManager instance for querying the database
    @ensures Accurate statistics are retrieved and calculated for each user
    """
    def __init__(self, db_manager):
        self.db_manager = db_manager

    """
    Retrieve analytics data for the current user, including the number of quizzes taken,
    total questions answered, and average score.
    @requires The user to be logged in (i.e., their email stored in session)
    @ensures Returns a dictionary with quiz analytics for the user
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

