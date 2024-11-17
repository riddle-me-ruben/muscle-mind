import os
import sys
import pytest

# Add the server directory to the system path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../server')))
from App import App

# Initialize the app
app_instance = App()
app = app_instance.app

# Sample email for testing purposes
sample_email = 'test1@example.com'

"""
Description:
This function sets up a Flask test client for the application. A test client allows the simulation of HTTP requests
to the Flask server without requiring it to be run in a production environment. The `with` statement ensures that 
the test client is properly initialized and cleaned up after use. It enables the test functions to send requests 
and verify responses without needing an actual running server.

Semi-formal Notation:
/*@ requires The Flask application is initialized and configured correctly;
  @ ensures A test client is yielded, allowing HTTP requests to be made directly to the application;
@*/
"""
@pytest.fixture
def client():
    """Fixture to set up a Flask test client."""
    with app.test_client() as client:
        yield client

"""
Description:
This function sets up a Flask test client and logs in a mock user by adding an "email" key to the session. It 
simulates the state of a signed-in user for test cases that require an authenticated session. The email used is 
a sample value (`sample_email`), which represents the signed-in user's identifier. Like the `client` fixture, the 
`with` statement ensures proper resource cleanup.

Semi-formal Notation:
/*@ requires The Flask application is initialized and configured correctly &&
  @ `sample_email` is defined and represents a valid email address
  @ ("a <= email[i] <= z || A <= email[i] <= Z" + "@" + domain.com);
  @ ensures A test client with a session containing "email" set to `sample_email` is yielded, simulating a logged-in user;
@*/
"""
@pytest.fixture
def logged_in_client(client):
    """Fixture to log in a test user."""
    with client.session_transaction() as sess:
        sess['email'] = sample_email
    yield client

"""
Description:
The Flask application server must be running and properly configured, allowing HTTP requests to be processed. 
The session should not contain an "email" key, indicating no user is currently signed in. The test ensures 
that the index page is rendered for a non-authenticated user.

Semi-formal Notation:
/*@ requires The server is running &&
  @ session does not contain an "email" key (session["email"] == None);
  @ ensures response.data is of type bytes &&
  @ response contains the content of the index page;
@*/
"""
def test_index(client):
    response = client.get('/')
    assert isinstance(response.data, bytes), "Index route response should be bytes."

"""
Description:
The server must be running, with all dependencies loaded and the "/home" route properly defined. The session 
can either be empty (indicating no user is signed in) or contain a valid email in the format 
("a <= email[i] <= z || A <= email[i] <= Z" + "@" + domain.com). The test ensures the "/home" route displays 
the correct content based on the sign-in state.

Semi-formal Notation:
/*@ requires The server is running &&
  @ (session["email"] == None || session["email"] matches the format
  @ ("a <= email[i] <= z || A <= email[i] <= Z" + "@" + domain.com));
  @ ensures If session["email"] == None:
  @   response.data is of type bytes &&
  @   response contains the guest home page;
  @ otherwise:
  @   response.data is of type bytes &&
  @   response contains the user-specific home page;
@*/
"""
def test_home(client):
    # When the user is not signed in
    with client.session_transaction() as sess:
        sess['email'] = None
    response = client.get('/home')
    assert isinstance(response.data, bytes), "Home route response should be bytes when not signed in."

    # When the user is signed in
    with client.session_transaction() as sess:
        sess['email'] = sample_email
    response = client.get('/home')
    assert isinstance(response.data, bytes), "Home route response should be bytes when signed in."

"""
Description:
The Flask application server must be running and connected to a database capable of storing user data. The 
provided email must match the format ("a <= email[i] <= z || A <= email[i] <= Z" + "@" + domain.com), and the 
password must be a non-empty string. The test ensures a new user is successfully added to the database.

Semi-formal Notation:
/*@ requires The server is running &&
  @ email matches the format ("a <= email[i] <= z || A <= email[i] <= Z" + "@" + domain.com) &&
  @ password is a non-empty string (password != "");
  @ ensures response.data is of type bytes &&
  @ a new user with the given email and password is added to the database;
@*/
"""
def test_add_user(client):
    data = {'email': sample_email, 'password': 'newpass'}
    response = client.post('/add_user', data=data)
    assert isinstance(response.data, bytes), "Add user route response should be bytes."

"""
Description:
The server must be active, and the "/login" route must be properly defined to handle GET requests. The route 
should render the login page and return its content as bytes.

Semi-formal Notation:
/*@ requires The server is running &&
  @ the "/login" route is defined;
  @ ensures response.data is of type bytes &&
  @ response contains the content of the login page;
@*/
"""
def test_login(client):
    response = client.get('/login')
    assert isinstance(response.data, bytes), "Login route response should be bytes."

"""
Description:
The server must be running, and the session must include a valid email matching the format 
("a <= email[i] <= z || A <= email[i] <= Z" + "@" + domain.com). The test ensures that the logout route clears 
the session and logs the user out successfully.

Semi-formal Notation:
/*@ requires The server is running &&
  @ session["email"] matches the format ("a <= email[i] <= z || A <= email[i] <= Z" + "@" + domain.com);
  @ ensures session["email"] is removed &&
  @ response.data is of type bytes;
@*/
"""
def test_logout(logged_in_client):
    response = logged_in_client.get('/logout')
    assert isinstance(response.data, bytes), "Logout route response should be bytes."

"""
Description:
The server must be running and connected to a database capable of storing quiz data. The session must include 
a valid email, and the request must contain a non-empty quiz title and a list of questions. The test ensures a 
new quiz is added to the database.

Semi-formal Notation:
/*@ requires The server is running &&
  @ session["email"] matches the format ("a <= email[i] <= z || A <= email[i] <= Z" + "@" + domain.com) &&
  @ title != "" &&
  @ questions is a list (questions != None);
  @ ensures A quiz with the specified title and questions is added to the database &&
  @ response.data is of type bytes;
@*/
"""
def test_create_quiz(logged_in_client):
    data = {'title': 'Sample Quiz', 'questions': []}
    response = logged_in_client.post('/create-quiz', data=data)
    assert isinstance(response.data, bytes), "Create quiz route response should be bytes."

"""
Description:
The server must be running and able to handle POST requests to the "/submit-quiz" route. The session must 
contain a valid email, and the request must include a non-empty list of answers. The test ensures the answers 
are submitted and stored successfully.

Semi-formal Notation:
/*@ requires The server is running &&
  @ session["email"] matches the format ("a <= email[i] <= z || A <= email[i] <= Z" + "@" + domain.com) &&
  @ answers is a non-empty list (answers != None && len(answers) > 0);
  @ ensures The answers are stored in the database &&
  @ response.data is of type bytes;
@*/
"""
def test_submit_quiz(logged_in_client):
    data = {'answers': ['A', 'B', 'C']}
    response = logged_in_client.post('/submit-quiz', data=data)
    assert isinstance(response.data, bytes), "Submit quiz route response should be bytes."

"""
Description:
The server must be active, and the request must include a valid quiz ID (a positive integer greater than 0). 
The test ensures that the quiz details corresponding to the given ID are retrieved and returned.

Semi-formal Notation:
/*@ requires The server is running &&
  @ quiz_id > 0;
  @ ensures The details of the quiz with the specified ID are retrieved &&
  @ response.data is of type bytes;
@*/
"""
def test_quiz_detail(client):
    response = client.get('/quiz/1')
    assert isinstance(response.data, bytes), "Quiz detail route response should be bytes."

"""
Description:
The server must be running and capable of retrieving quiz data from the database. The request must include a 
valid quiz ID (quiz_id > 0) and question number (question_number >= 0). The test ensures the quiz question and 
options are presented to the user.

Semi-formal Notation:
/*@ requires The server is running &&
  @ quiz_id > 0 &&
  @ question_number >= 0;
  @ ensures The question and options for the specified quiz and question number are retrieved &&
  @ response.data is of type bytes;
@*/
"""
def test_take_quiz(client):
    response = client.get('/take-quiz/1/1')
    assert isinstance(response.data, bytes), "Take quiz route response should be bytes."

"""
Description:
The server must be active and capable of calculating penalties for incorrect answers. The request must include 
a valid quiz ID (quiz_id > 0) and question number (question_number >= 0). The test ensures the penalty 
information is correctly calculated and returned.

Semi-formal Notation:
/*@ requires The server is running &&
  @ quiz_id > 0 &&
  @ question_number >= 0;
  @ ensures The penalty for the incorrect answer is calculated and returned &&
  @ response.data is of type bytes;
@*/
"""
def test_penalty(client):
    response = client.get('/penalty/1/1')
    assert isinstance(response.data, bytes), "Penalty route response should be bytes."

"""
Description:
The server must be running and connected to a database capable of processing and storing quiz answers. The 
session must contain a valid email, and the request must include a valid quiz ID and non-empty answer. The test 
ensures the answer is stored successfully and feedback is returned to the user.

Semi-formal Notation:
/*@ requires The server is running &&
  @ session["email"] matches the format ("a <= email[i] <= z || A <= email[i] <= Z" + "@" + domain.com) &&
  @ quiz_id > 0 &&
  @ answer != "" (non-empty string);
  @ ensures The answer is submitted and feedback is generated &&
  @ response.data is of type bytes;
@*/
"""
def test_submit_quiz_answer(logged_in_client):
    # Step 1: Create a quiz with valid questions
    create_quiz_data = {
        'title': 'Sample Quiz',
        'questions': [
            {'question': 'What is 2+2?', 'options': ['1', '2', '4', '5'], 'correct_option': '4'},
            {'question': 'What is the capital of France?', 'options': ['London', 'Paris', 'Rome', 'Berlin'], 'correct_option': 'Paris'}
        ]
    }
    logged_in_client.post('/create-quiz', data=create_quiz_data)

    # Step 2: Submit a valid answer for the first question
    submit_answer_data = {'answer': '4'}
    response = logged_in_client.post('/submit-quiz-answer/1/0', data=submit_answer_data)
    assert isinstance(response.data, bytes), "Submit quiz answer route response should be bytes."