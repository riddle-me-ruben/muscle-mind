from flask import Flask, render_template, redirect, url_for, session
from DatabaseManager import DatabaseManager
from QuizManager import QuizManager
from UserManager import UserManager
from DataAnalyticsManager import DataAnalyticsManager
from QuizRetrievalManager import QuizRetrievalManager
from dotenv import load_dotenv
import os

"""
The App class initializes and manages the Flask application for the Muscle-Mind system, acting as the central 
mediator between the database subsystem and the quiz management subsystem. This class configures the app, 
sets up environment variables, manages user sessions, and provides a streamlined interface to handle quiz 
creation, user management, and data retrieval from the database.

@requires:
- Environment variables, including Flask app configurations and MySQL credentials, must be set.
- DatabaseManager, QuizManager, and UserManager are instantiated and correctly set up to handle database and 
    user operations.

@ensures:
- The app is fully configured and ready to mediate user interactions with the quiz and database subsystems.
- Requests are directed to the correct endpoints, enabling efficient handling of quiz, user, and data operations.
"""
class App:
    """
    Initialize the App class and set up the Flask app, database manager, and other managers
    @requires Environment variables to be loaded, Flask app to be initialized
    @ensures Flask app and all managers (db_manager, quiz_manager, user_manager) are set up
    """
    def __init__(self):
        load_dotenv()
        self.app = Flask(__name__, static_folder=os.path.join(os.path.dirname(__file__), '../../static'), template_folder='../client')
        self.app.config['SECRET_KEY'] = os.getenv('SECRET_KEY')
        
        # Initialize managers
        self.db_manager = DatabaseManager(self.app)
        self.quiz_manager = QuizManager(self.db_manager)
        self.user_manager = UserManager(self.db_manager, session)
        self.analytics_manager = DataAnalyticsManager(self.db_manager)
        self.quiz_retrieval_manager = QuizRetrievalManager(self.db_manager, self.analytics_manager)

        # Set up routes
        self.initialize_routes()

    """
    Initialize the routes for the Flask app
    @requires self.app to be initialized and Flask instance to be active
    @ensures All app routes are defined and linked to corresponding methods
    """
    def initialize_routes(self):
        # Define routes with various HTTP methods
        route_definitions = [
            ('/', 'index', self.index, ['GET']),
            ('/add_user', 'add_user', self.user_manager.add_user, ['POST']),
            ('/login', 'login', self.user_manager.login, ['GET', 'POST']),
            ('/home', 'home', self.home, ['GET']),
            ('/logout', 'logout', self.user_manager.logout, ['GET']),
            ('/create-quiz', 'create_quiz_route', self.quiz_manager.create_quiz, ['GET', 'POST']),
            ('/submit-quiz', 'submit_quiz_route', self.quiz_manager.submit_quiz, ['POST']),
            ('/quiz-detail/<int:quiz_id>', 'quiz_detail_route', self.quiz_manager.quiz_detail, ['GET']),
            ('/take-quiz/<int:quiz_id>/<int:question_num>', 'take_quiz_route', self.quiz_manager.take_quiz, ['GET', 'POST']),
            ('/score/<int:quiz_id>/<int:score>/<int:total>', 'score_route', self.quiz_manager.score, ['GET']),
            ('/submit-answer/<int:quiz_id>/<int:question_num>', 'submit_quiz_answer_route', self.quiz_manager.submit_quiz_answer, ['POST']),
            ('/penalty/<int:quiz_id>/<int:question_num>', 'penalty_route', self.quiz_manager.penalty, ['GET']),
            ('/delete-quiz/<int:quiz_id>', 'delete_quiz_route', self.quiz_manager.delete_quiz, ['POST']),
            ('/view_other_user_quizzes', 'view_other_user_quizzes', self.quiz_retrieval_manager.view_other_user_quizzes, ['GET', 'POST']),
            ('/restore_user_quizzes', 'restore_user_quizzes', self.quiz_retrieval_manager.restore_user_quizzes, ['POST'])
        ]

        # Loop through route definitions to add them to the app
        for rule, endpoint, view_func, methods in route_definitions:
            self.app.add_url_rule(rule, endpoint, view_func, methods=methods)

    """
    Render the index page or redirect to home if user is signed in
    @requires session to track if user is signed in
    @ensures Index page is rendered or redirects to home
    """
    def index(self):
        if self.user_manager.is_signed_in():
            return redirect(url_for('home'))
        return render_template('index.html')

    """
    Render the home page showing quizzes created by the user
    user_email: str - Email of the user from the session
    @requires user must be signed in and user_email stored in session
    @ensures Home page is rendered with the user's quizzes
    """
    def home(self):
        if not self.user_manager.is_signed_in():
            return redirect(url_for('login'))
        # Check if there's an other_user_email in session; if so, show their quizzes
        other_user_email = session.get('other_user_email')
        if other_user_email:
            quizzes = self.quiz_manager.get_user_quizzes(other_user_email)
            analytics = None  # Do not show analytics for other user's quizzes
        else:
            session.pop('other_user_email', None)
            user_email = session['email']
            quizzes = self.quiz_manager.get_user_quizzes(user_email)
            analytics = self.analytics_manager.get_user_analytics()    
        return render_template('home.html', quizzes=quizzes, analytics=analytics)

    """
    Start the Flask app in debug mode
    @requires Flask app instance to be initialized
    @ensures The Flask app is running in debug mode
    """
    def run(self):
        port = int(os.environ.get('PORT', 10000))  # Use PORT environment variable
        self.app.run(host='0.0.0.0', port=port, debug=True)
        self.app.run(debug=True)

"""
Main entry point for running the Flask app
@requires App class to be initialized
@ensures The Flask app runs with debugging enabled
"""
def main():
    app_instance = App()
    app_instance.run()

if __name__ == '__main__':
    main()